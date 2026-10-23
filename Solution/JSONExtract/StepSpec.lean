import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Model
import Solution.JSONExtract.StepTheorems

/-!
# Statements of the per-position gadget (`JSONExtract`)

`Step.lean` checks one position of the automaton run.  This file carries
everything that can be said *about* a position without looking at the
circuit: the gadget's input/output structures, the encoding of a
`Model.Regs` as the gadget's `*Prev` / `*Next` field vectors, the gadget's
`Assumptions` / `Spec` / `ProverAssumptions`, and the intermediate `RowSpec`
(the exact field identities the rows of `Step.main` enforce, written in the
value-level twins of `StepTheorems.lean`).

## The invariant

`Step` is a `GeneralFormalCircuit`.  Its inputs contain the *witnessed* state
after the byte (`stNext`, `subNext`, the registers, ...), so the rows that
compare `Next` with the computed transition hold only when `Next` really is
the honest successor.  A `FormalCircuit` has a single `Assumptions` used by
both directions, and completeness would need "`Next` encodes `Model.step` of
`Prev`" -- a statement `Main.soundness` could never supply.  So:

* `Assumptions` (soundness) only bounds the four inputs the *child gadgets*
  need (`byte < 256` for `ByteClass`, `hexAcc < 4096` for the `LessThan 16`
  range of the emitted code point, `kIdx < 16` and `ofs < 129` for the two
  `OneHot`s).
* `Spec` says, for *every* `r : Model.Regs` the `*Prev` half encodes:
  the activity row `accmNext = accmPrev + lenFlag`; when the position is
  inactive (`accmNext = 1`) every `Next` field equals its `Prev` field and the
  outputs are the signals of the frozen position; when it is active
  (`accmNext = 0`) the two state vectors are the *indicator vectors of the
  model's `Option`-valued transitions* (all-zero when there is no transition,
  which the next position's one-hot row then refutes), a transition of both
  automata implies `Model.step` succeeds (this is the content of the two
  routing rows: the value fits its slot's cap and a string claim's code point
  is ASCII), and for the successor `r'` every `Next` field encodes `r'` and
  the outputs are `Model.signals`.  The active branch also states that the
  three successor registers are *in range* whether or not the automata
  transition: `Main` applies this very specification at the next position (to
  refute an all-zero `Next`), and for that it must first discharge
  `Assumptions` there.  `Spec` also exports the one-hot shape of the `*Prev`
  state vectors, which is how `Main` learns that the *previous* position did
  have a transition.
* `ProverAssumptions` (completeness) is the honest-prover view: the `*Prev`
  half encodes some well-formed `r`, the activity row holds, and the `*Next`
  half encodes `r` (inactive) or `Model.step r byte` (active), and the output
  slot cell this position writes already holds the routed value.  The ten
  slot-routing rows and the ASCII row are *not* gated by the activity flag, so
  the inactive branch also has to say that the position routes nothing; in
  `Main` that is free, because a frozen position sits in `END`, where neither a
  string code point nor an integer digit is emitted.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Circomlib
open Model (nSt nSub nClaims kIdxMax ofsMax St Sub Claim Regs)
open ByteClass (ind)

namespace Step

open Model.St Model.Sub

/-- `2^17 < p`, for `LessThan 16`. -/
theorem two_pow_17_lt' : 2 ^ 17 < circomPrime := two_pow_17_lt

instance : Fact (circomPrime > 2) := ⟨by decide⟩

/-- Everything one position sees. `*Prev` is the state before the byte,
    `*Next` the witnessed state after it. -/
structure Inputs (F : Type) where
  byte : F
  /-- `lenFlags[i]`, the one-hot of `len` at this position -/
  lenFlag : F
  /-- prefix sum of `lenFlags` before / after this position -/
  accmPrev : F
  accmNext : F
  stPrev : Vector F nSt
  stNext : Vector F nSt
  subPrev : Vector F nSub
  subNext : Vector F nSub
  hexAccPrev : F
  hexAccNext : F
  kIdxPrev : F
  kIdxNext : F
  mPrev : Vector F nClaims
  mNext : Vector F nClaims
  claimPrev : Vector F nClaims
  claimNext : Vector F nClaims
  ofsPrev : F
  ofsNext : F
  nMemPrev : F
  nMemNext : F
  /-- the circuit output, whose slot cells this position may write -/
  out : Output F
deriving ProvableStruct

/-- The per-position signals the end pins of `main` consume. -/
structure Outputs (F : Type) where
  /-- the key closing at this position is claim `k` -/
  match_ : Vector F nClaims
  /-- a value is emitted at this position for claim `k` -/
  vEmitK : Vector F nClaims
  /-- a `-` is consumed at this position for claim `k` -/
  minusK : Vector F nClaims
  /-- `true` completes at this position for the boolean claim -/
  trueK : F
deriving ProvableStruct

abbrev E := Expression (F circomPrime)

/-! ## Encoding a model state as the gadget's field vectors -/

/-- The `*Prev` half of the inputs encodes the model registers `r`. -/
def EncodesPrev (inp : Inputs (F circomPrime)) (r : Regs) : Prop :=
  (∀ j : Fin nSt, inp.stPrev[j] = if j = r.st then 1 else 0) ∧
  (∀ j : Fin nSub, inp.subPrev[j] = if j = r.sub then 1 else 0) ∧
  inp.hexAccPrev = (r.hexAcc : F circomPrime) ∧
  inp.kIdxPrev = (r.kIdx : F circomPrime) ∧
  (∀ k : Claim, inp.mPrev[k] = if r.m[k] then 1 else 0) ∧
  (∀ k : Claim, inp.claimPrev[k] = if r.claim = some k then 1 else 0) ∧
  inp.ofsPrev = (r.ofs : F circomPrime) ∧
  inp.nMemPrev = (r.nMem : F circomPrime)

/-- The `*Next` half of the inputs encodes the model registers `r`. -/
def EncodesNext (inp : Inputs (F circomPrime)) (r : Regs) : Prop :=
  (∀ j : Fin nSt, inp.stNext[j] = if j = r.st then 1 else 0) ∧
  (∀ j : Fin nSub, inp.subNext[j] = if j = r.sub then 1 else 0) ∧
  inp.hexAccNext = (r.hexAcc : F circomPrime) ∧
  inp.kIdxNext = (r.kIdx : F circomPrime) ∧
  (∀ k : Claim, inp.mNext[k] = if r.m[k] then 1 else 0) ∧
  (∀ k : Claim, inp.claimNext[k] = if r.claim = some k then 1 else 0) ∧
  inp.ofsNext = (r.ofs : F circomPrime) ∧
  inp.nMemNext = (r.nMem : F circomPrime)

/-- Two live key matchers agree on the key consumed so far.

This is the one thing beyond the register bounds that a position needs about
the state before it.  The circuit sets *every* matching claim flag at a key
close (`claimNext[k] = match_[k]`), while `Model.step` stores the *first*
matching claim; the two agree exactly when at most one claim can match, which
is what this invariant gives (two claims whose names have the same length and
agree on every consumed code point would otherwise both match).  It holds
along the run -- `Model.Regs.init` has no live matcher, and `Model.step`
preserves it -- so `Main` threads it forward exactly like the bounds below. -/
def MatchInv (r : Regs) : Prop :=
  ∀ k k' : Claim, r.m[k] = true → r.m[k'] = true →
    ∀ j, j < r.kIdx → Model.nameAt k j = Model.nameAt k' j

/-- The bound `hexAcc` obeys in each sub state: the `\uXXXX` states `H1 → H2 → H3`
each admit one more hex digit, and outside them the accumulator is cleared.  This is
sharper than `hexAcc < 4096` and is what makes the *successor* accumulator fit the
`LessThan 16` range of the next position: `16 · hexAcc + hexVal b < 4096` needs
`hexAcc < 256` at `H3`. -/
def hexCap (s : Sub) : ℕ :=
  if s = Sub.H1 then 1 else if s = Sub.H2 then 16 else if s = Sub.H3 then 256 else 4096

theorem hexCap_le (s : Sub) : hexCap s ≤ 4096 := by unfold hexCap; split_ifs <;> omega

/-- The register bounds the child gadgets need, at the model level, plus the
matcher invariant the claim register's update needs and the one place where
the circuit's saturation and the model's `min` could part company.

The offset register is `inVal · ofs + vEmit · [ofs ≠ 128]` in the circuit and
`min ((if inVal then ofs else 0) + vEmit) 128` in the model.  The two agree
except when a value character is emitted at a state *outside* a value with the
offset already saturated: the circuit clears it to `0`, the model to `1`.  The
only such state is `PVAL` (a digit read there starts an integer), where the
offset is always `0` along the run, because every transition into `PVAL` comes
from a state outside a value and emits nothing. -/
def WFRegs (r : Regs) : Prop :=
  r.hexAcc < 4096 ∧ r.kIdx < kIdxMax ∧ r.ofs < ofsMax ∧ MatchInv r ∧
    (r.st = St.PVAL → r.ofs = 0) ∧ r.hexAcc < hexCap r.sub

/-! ## Reading the output slots -/

/-- Cell `t` of claim `k`'s output slot (`0` past the slot's cap, and for the
boolean claim, which has no cells). -/
def outCell (o : Output (F circomPrime)) (k : Claim) (t : ℕ) : F circomPrime :=
  match k.val with
  | 0 => o.iss.bytes[t]?.getD 0
  | 1 => o.sub.bytes[t]?.getD 0
  | 2 => o.aud.bytes[t]?.getD 0
  | 3 => o.azp.bytes[t]?.getD 0
  | 4 => o.hd.bytes[t]?.getD 0
  | 5 => o.email.bytes[t]?.getD 0
  | 7 => o.nonce.bytes[t]?.getD 0
  | 8 => o.atHash.bytes[t]?.getD 0
  | 9 => o.iat.digits[t]?.getD 0
  | 10 => o.exp.digits[t]?.getD 0
  | _ => 0

/-- The per-position signals the gadget returns, read against the model. -/
def OutSignals (out : Outputs (F circomPrime)) (r : Regs) (sg : Model.Signals) : Prop :=
  (∀ k : Claim, out.match_[k] = if sg.match_[k] then 1 else 0) ∧
  (∀ k : Claim, out.vEmitK[k] = if sg.vEmit ∧ r.claim = some k then 1 else 0) ∧
  (∀ k : Claim, out.minusK[k] = if sg.minusFlag ∧ r.claim = some k then 1 else 0) ∧
  out.trueK = if sg.trueDone ∧ r.claim = some 6 then 1 else 0

/-- The routed value reaches the cell of the claim's slot the offset selects. -/
def WritesCell (inp : Inputs (F circomPrime)) (r : Regs) (sg : Model.Signals) : Prop :=
  ∀ k : Claim, sg.write = true → r.claim = some k →
    outCell inp.out k r.ofs = ((sg.valOut : ℕ) : F circomPrime)

/-! ## The statements of the gadget -/

/-- What one position says about a model state its `*Prev` half encodes. -/
def SpecOf (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) (r : Regs) : Prop :=
  let b := inp.byte.val
  let stepSt := Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b
  let stepSub := Model.stepSub (Model.inStr r.st) r.sub b
  -- activity is the prefix sum of the length flags
  inp.accmNext = inp.accmPrev + inp.lenFlag ∧
  -- an inactive position freezes everything
  (inp.accmNext = 1 →
    EncodesNext inp r ∧ OutSignals out r (Model.signals r b r.st)) ∧
  -- an active position takes the transition
  (inp.accmNext = 0 →
    (∀ j : Fin nSt, inp.stNext[j] = optInd stepSt j) ∧
    (∀ j : Fin nSub, inp.subNext[j] = optInd stepSub j) ∧
    -- the register rows bound the successor registers whether or not the
    -- automata transition, which is what lets `Main` apply this very
    -- specification at the *next* position (and so refute an all-zero `Next`)
    inp.hexAccNext.val < 4096 ∧ inp.kIdxNext.val < kIdxMax ∧ inp.ofsNext.val < ofsMax ∧
    -- the two routing rows: a transition of both automata is a full step
    (stepSub.isSome → stepSt.isSome → (Model.step r b).isSome) ∧
    ∀ r' : Regs, Model.step r b = some r' →
      EncodesNext inp r' ∧ OutSignals out r (Model.signals r b r'.st) ∧
      WritesCell inp r (Model.signals r b r'.st))

/-- Soundness assumptions: only the bounds the child gadgets need.  `Main`
supplies them from the encoding of the run's registers. -/
def Assumptions (inp : Inputs (F circomPrime)) (_d : ProverData (F circomPrime)) : Prop :=
  inp.byte.val < 256 ∧ inp.hexAccPrev.val < 4096 ∧
  inp.kIdxPrev.val < kIdxMax ∧ inp.ofsPrev.val < ofsMax

/-- The soundness specification. The one-hot shape of the `*Prev` state
vectors is a *conclusion*: it is how `Main` learns, at position `i + 1`, that
position `i` did have a transition. -/
def Spec (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime))
    (_d : ProverData (F circomPrime)) : Prop :=
  (∀ j : Fin nSt, IsBool inp.stPrev[j]) ∧ (∑ j : Fin nSt, inp.stPrev[j]) = 1 ∧
  (∀ j : Fin nSub, IsBool inp.subPrev[j]) ∧ (∑ j : Fin nSub, inp.subPrev[j]) = 1 ∧
  ∀ r : Regs, WFRegs r → EncodesPrev inp r → SpecOf inp out r

/-- The honest prover's view: the `*Next` half is the model's step. -/
def ProverAssumptions (inp : Inputs (F circomPrime))
    (_d : ProverData (F circomPrime)) (_h : ProverHint (F circomPrime)) : Prop :=
  inp.byte.val < 256 ∧
  ∃ r : Regs, WFRegs r ∧ EncodesPrev inp r ∧
    inp.accmNext = inp.accmPrev + inp.lenFlag ∧
    ((inp.accmNext = 1 ∧ EncodesNext inp r ∧
        (Model.signals r inp.byte.val r.st).write = false) ∨
     (inp.accmNext = 0 ∧ ∃ r' : Regs, Model.step r inp.byte.val = some r' ∧
        EncodesNext inp r' ∧ WritesCell inp r (Model.signals r inp.byte.val r'.st)))

/-! ## The rows

The exact field identities the rows of `Step.main` enforce, in the
value-level twins of `StepTheorems.lean`.  `Step.soundness` proves this from
the constraints, `Step.completeness` proves the constraints from it; both
directions of the model bridge below go through it. -/

def RowSpec (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  let byte := inp.byte
  let stP := inp.stPrev
  let stN := inp.stNext
  let sbP := inp.subPrev
  let clP := inp.claimPrev
  let act : F circomPrime := 1 - inp.accmNext
  let cls := classesOf byte.val
  let kOH := ohOf kIdxMax inp.kIdxPrev
  let oOH := ohOf ofsMax inp.ofsPrev
  -- the claim register and the matcher registers are boolean, at most one claim
  (∀ k : Claim, IsBool clP[k]) ∧
  (∀ k : Claim, IsBool inp.mPrev[k]) ∧
  IsBool (kUnk clP) ∧
  -- activity
  inp.accmNext = inp.accmPrev + inp.lenFlag ∧
  -- the sub automaton
  (∀ j : Fin nSub, IsBool sbP[j]) ∧ (∑ j : Fin nSub, sbP[j]) = 1 ∧
  (∀ j : Fin nSub, inp.subNext[j] = sbP[j] +
    act * (inStr stP * SubAutomaton.massVal cls sbP j.val
      + (if j.val = 0 then 1 - inStr stP else 0) - sbP[j])) ∧
  -- the main automaton
  (∀ j : Fin nSt, IsBool stP[j]) ∧ (∑ j : Fin nSt, stP[j]) = 1 ∧
  (∀ j : Fin nSt, stN[j] = stP[j] +
    act * (MainAutomaton.plainMassVal cls (closeQuote byte sbP) stP j.val
      + MainAutomaton.gatedMassVal cls (closeQuote byte sbP) (kinds clP) stP j.val - stP[j])) ∧
  -- the `\uXXXX` accumulator
  inp.hexAccNext = inp.hexAccPrev +
    act * (inH sbP * (16 * inp.hexAccPrev + hexVal byte) - inp.hexAccPrev) ∧
  -- the key index
  inp.kIdxPrev.val < kIdxMax ∧
  inp.kIdxNext = inp.kIdxPrev +
    act * (stP[KEY] * (inp.kIdxPrev + emit byte stP sbP * (1 - kOH[kIdxMax - 1])) - inp.kIdxPrev) ∧
  -- the key matchers and the match flags
  (∀ k : Claim, inp.mNext[k] = inp.mPrev[k] +
    act * (keyStart stP stN + stP[KEY] * (inp.mPrev[k] *
      (1 - emit byte stP sbP * (1 - eqCp k byte stP sbP inp.hexAccPrev inp.kIdxPrev)))
      - inp.mPrev[k])) ∧
  (∀ k : Claim, out.match_[k] = matchOf k byte stP sbP inp.mPrev inp.kIdxPrev) ∧
  -- the claim register
  (∀ k : Claim, inp.claimNext[k] = clP[k] +
    act * (out.match_[k] + hold byte stP stN sbP * clP[k] - clP[k])) ∧
  -- the value offset
  inp.ofsPrev.val < ofsMax ∧
  inp.ofsNext = inp.ofsPrev +
    act * (inVal stP * inp.ofsPrev + vEmit byte stP sbP * (1 - oOH[ofsMax - 1]) - inp.ofsPrev) ∧
  -- the per-position signals
  (∀ k : Claim, out.vEmitK[k] = vEmit byte stP sbP * clP[k]) ∧
  (∀ k : Claim, out.minusK[k] = minusFlag byte stP * clP[k]) ∧
  out.trueK = trueDone byte stP * clP[6] ∧
  -- the member counter
  inp.nMemNext = inp.nMemPrev + keyStart stP stN ∧
  -- routing
  write byte stP sbP clP * (selected clP inp.ofsPrev inp.out
    - valOut byte stP sbP inp.hexAccPrev) = 0 ∧
  write byte stP sbP clP * (existsIn clP inp.ofsPrev - 1) = 0 ∧
  write byte stP sbP clP * stP[STR] * (1 - ltAscii byte stP sbP inp.hexAccPrev) = 0

/-! ## Peeling the operation list structurally

`circuit_norm` cannot normalise `ConstraintsHold.Soundness` on `Step.main`: it
reduces the concrete `Fin.foldl`s and `ProvableStruct` element vectors of the
child gadgets' interfaces (129-wide offset one-hots, 128-cell slots), and the
`toElements` / `Array.append` reductions blow the heartbeat budget long before
the operation list is peeled (measured: `circuit_proof_start` on `Step.main`
runs out at 4M heartbeats after 3m25s / 3.8 GB, with `componentsToElements`,
`Array.append` and `Eq.rec` each unfolded >100k times).  The lemmas below are
the *only* rewrites the peel needs: one per `do`-block former, keyed on the
former rather than on the operation list, so a single `simp only` with this set
splits `Step.main` into its 63 top-level rows in about two seconds without ever
unfolding a child's interface.

The recipe that works (measured at ~20 s, 2.9 GB for the whole peel):

```
  circuit_proof_start_core                      -- the full tactic times out
  simp +instances only [circuit_norm] at h_input
  dsimp only [Assumptions] at *
  dsimp only [Spec] at *
  dsimp +instances only [main, mul, freeze] at *
  dsimp only [ElaboratedCircuit.withData, ElaboratedCircuit.output]
  dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *
  provable_struct_simp
  -- (1) split the operation list
  simp only [sbind, szero, spure, ssub, ssubA, sassert, sforEach, smapFinRange,
    llbind, llzero, llpure, llsub, llsubA, llassert, osub, osubA,
    Circuit.forEach.localLength_eq, Circuit.mapFinRange.localLength_eq,
    Circuit.mapFinRange.output_eq, Vector.getElem_finRange, Model.nClaims,
    Nat.add_assoc, Nat.add_zero, Nat.zero_add,
    Mul.circuit_localLength, Mul.circuit_output, byteClass_localLength,
    oneHot_localLength, oneHot_output, matcher_localLength, matcher_output,
    routeSlot_localLength, routeSlot_output, subAutomaton_localLength,
    mainAutomaton_localLength, lessThan_localLength, lessThan_output] at h_holds
  -- (2) resolve the child interfaces (never `circuit_norm` on the whole thing)
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, subAutomaton_Assumptions,
    mainAutomaton_Assumptions, routeSlot_Assumptions, matcher_Assumptions,
    byteClass_Assumptions, oneHot_Assumptions, lessThan_Assumptions,
    subAutomaton_Spec, mainAutomaton_Spec, routeSlot_Spec, matcher_Spec,
    byteClass_Spec_iff, oneHot_Spec_iff, lessThan_Spec, true_implies,
    Expression.eval, eval_cls, eval_mulIn, eval_oneHotIn, eval_subAutoIn,
    eval_mainAutoIn, eval_matcherIn, eval_routeSlotIn] at h_holds
  dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at h_holds
  simp only [Mul.circuit_Spec, eval_cls, eval_mulIn, eval_oneHotIn, eval_subAutoIn,
    eval_mainAutoIn, eval_matcherIn, eval_routeSlotIn, CircuitType.eval_expr,
    CircuitType.eval_var_field, eval_sub, eval_add, eval_mul, eval_neg,
    Expression.eval] at h_holds
  obtain ⟨hBC, hClB, hMB, hKU, hAccm, hCQ, hSubA, hMainA, hIP, hIE, hIH4, hIC1, hEP, hEE,
    hEU, hE8, hHD, hHU, hHL, hCPP, hCPE, hCPU, hHAN, ⟨hFHd, hFHz⟩, hKS, hKC, hOH1, hKInc,
    hKNew, ⟨hFKd, hFKz⟩, hMat, hClaimLoop, hSE, hDE, hW, hVOS, hVOD, hOH2, hOInc, hOKept,
    ⟨hFOd, hFOz⟩, hVEK, hMF, hMK, hTD, hTK, hNMem, hR0, hR1, hR2, hR3, hR4, hR5, hR7, hR8,
    hR9, hR10, hSel, hEx, hLT, hWS, hWSz, hTrue⟩ := h_holds
```

Two further traps found while chaining the 63 rows into `RowSpec`:

* `set C := ByteClass.circuit.output input_var_byte i₀` *before* any `rw` that
  mentions a classifier flag.  Without it a single `rw [c_isQuote] at hCQ`
  costs over 1M heartbeats, because keyed matching `whnf`s the 44-field
  `varFromOffset`; with it the whole chain costs a few seconds.
* the one-hot outputs must be used *pointwise*: from `hKOH` (resp. `hOOH`),
  `have hKOHi := Vector.ext_iff.mp hKOH; simp only [Vector.getElem_map] at hKOHi`
  and then `simp only [hKOHi]`.  The whole-vector equation never matches,
  because the rows index the one-hot rather than passing it on. -/

section Peel
variable {F : Type} [FiniteField F] {α β : Type}

theorem sbind {env : Environment F} {f : Circuit F α} {g : α → Circuit F β} {n : ℕ} :
    ConstraintsHold.Soundness env ((f >>= g).operations n) ↔
      ConstraintsHold.Soundness env (f.operations n) ∧
      ConstraintsHold.Soundness env ((g (f.output n)).operations (n + f.localLength n)) :=
  Circuit.bind_forAllNoOffset

theorem szero {env : Environment F} {e : Expression F} {n : ℕ} :
    ConstraintsHold.Soundness env ((Circuit.assertZero e).operations n)
      ↔ Expression.eval env e = 0 := by
  simp [circuit_norm]

theorem spure {env : Environment F} {a : α} {n : ℕ} :
    ConstraintsHold.Soundness env ((pure a : Circuit F α).operations n) ↔ True := by
  simp [circuit_norm]

theorem ssub {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {env : Environment F} {circuit : FormalCircuit F Input Output} {b : Var Input F} {n : ℕ} :
    ConstraintsHold.Soundness env ((subcircuit circuit b).operations n) ↔
      (circuit.Assumptions (eval env b) →
        circuit.Spec (eval env b) (eval env (circuit.output b n))) := by
  simp [circuit_norm]

theorem ssubA {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {env : Environment F} {circuit : GeneralFormalCircuit F Input Output} {b : Var Input F}
    {n : ℕ} :
    ConstraintsHold.Soundness env ((subcircuitWithAssertion circuit b).operations n) ↔
      (circuit.Assumptions (eval env b) env.data →
        circuit.Spec (eval env b) (eval env (circuit.output b n)) env.data) := by
  simp [circuit_norm]

theorem sassert {Input : TypeMap} [ProvableType Input]
    {env : Environment F} {circuit : FormalAssertion F Input} {b : Var Input F} {n : ℕ} :
    ConstraintsHold.Soundness env ((assertion circuit b).operations n) ↔
      (circuit.Assumptions (eval env b) → circuit.Spec (eval env b)) := by
  simp [circuit_norm]

theorem cbind {env : ProverEnvironment F} {f : Circuit F α} {g : α → Circuit F β} {n : ℕ} :
    ConstraintsHold.Completeness env ((f >>= g).operations n) ↔
      ConstraintsHold.Completeness env (f.operations n) ∧
      ConstraintsHold.Completeness env ((g (f.output n)).operations (n + f.localLength n)) :=
  Circuit.bind_forAllNoOffset

theorem czero {env : ProverEnvironment F} {e : Expression F} {n : ℕ} :
    ConstraintsHold.Completeness env ((Circuit.assertZero e).operations n)
      ↔ Expression.eval env.toEnvironment e = 0 := by
  simp [circuit_norm]

theorem cpure {env : ProverEnvironment F} {a : α} {n : ℕ} :
    ConstraintsHold.Completeness env ((pure a : Circuit F α).operations n) ↔ True := by
  simp [circuit_norm]

theorem csub {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {env : ProverEnvironment F} {circuit : FormalCircuit F Input Output} {b : Var Input F}
    {n : ℕ} :
    ConstraintsHold.Completeness env ((subcircuit circuit b).operations n) ↔
      circuit.Assumptions (eval env b) := by
  simp [circuit_norm]

theorem csubA {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {env : ProverEnvironment F} {circuit : GeneralFormalCircuit F Input Output} {b : Var Input F}
    {n : ℕ} :
    ConstraintsHold.Completeness env ((subcircuitWithAssertion circuit b).operations n) ↔
      circuit.ProverAssumptions (eval env b) env.data env.hint := by
  simp [circuit_norm]

theorem cassert {Input : TypeMap} [ProvableType Input]
    {env : ProverEnvironment F} {circuit : FormalAssertion F Input} {b : Var Input F} {n : ℕ} :
    ConstraintsHold.Completeness env ((assertion circuit b).operations n) ↔
      (circuit.Assumptions (eval env b) ∧ circuit.Spec (eval env b)) := by
  simp [circuit_norm]

theorem wbind {env : ProverEnvironment F} {f : Circuit F α} {g : α → Circuit F β} {n : ℕ} :
    env.UsesLocalWitnessesCompleteness n ((f >>= g).operations n) ↔
      env.UsesLocalWitnessesCompleteness n (f.operations n) ∧
      env.UsesLocalWitnessesCompleteness (n + f.localLength n)
        ((g (f.output n)).operations (n + f.localLength n)) :=
  Circuit.ConstraintsHold.bind_usesLocalWitnesses n

theorem llbind {f : Circuit F α} {g : α → Circuit F β} {n : ℕ} :
    (f >>= g).localLength n
      = f.localLength n + (g (f.output n)).localLength (n + f.localLength n) :=
  Circuit.bind_localLength_eq f g n

theorem llzero {e : Expression F} {n : ℕ} : (Circuit.assertZero e).localLength n = 0 := rfl

theorem llpure {a : α} {n : ℕ} : (pure a : Circuit F α).localLength n = 0 := rfl

theorem llsub {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuit F Input Output} {b : Var Input F} {n : ℕ} :
    (subcircuit circuit b).localLength n = circuit.localLength b := rfl

theorem llsubA {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit F Input Output} {b : Var Input F} {n : ℕ} :
    (subcircuitWithAssertion circuit b).localLength n = circuit.localLength b := rfl

theorem llassert {Input : TypeMap} [ProvableType Input]
    {circuit : FormalAssertion F Input} {b : Var Input F} {n : ℕ} :
    (assertion circuit b).localLength n = circuit.localLength b := rfl

theorem osub {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuit F Input Output} {b : Var Input F} {n : ℕ} :
    (subcircuit circuit b).output n = circuit.output b n := rfl

theorem osubA {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit F Input Output} {b : Var Input F} {n : ℕ} :
    (subcircuitWithAssertion circuit b).output n = circuit.output b n := rfl

theorem obind {f : Circuit F α} {g : α → Circuit F β} {n : ℕ} :
    (f >>= g).output n = (g (f.output n)).output (n + f.localLength n) :=
  Circuit.bind_output_eq f g n

theorem opure {a : α} {n : ℕ} : (pure a : Circuit F α).output n = a := rfl

/-! ### The `UsesLocalWitnessesCompleteness` side of the peel -/

theorem wzero {env : ProverEnvironment F} {e : Expression F} {n m : ℕ} :
    env.UsesLocalWitnessesCompleteness m ((Circuit.assertZero e).operations n) ↔ True := by
  simp [circuit_norm]

theorem wpure {env : ProverEnvironment F} {a : α} {n m : ℕ} :
    env.UsesLocalWitnessesCompleteness m ((pure a : Circuit F α).operations n) ↔ True := by
  simp [circuit_norm]

theorem wsub {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {env : ProverEnvironment F} {circuit : FormalCircuit F Input Output} {b : Var Input F}
    {n m : ℕ} :
    env.UsesLocalWitnessesCompleteness m ((subcircuit circuit b).operations n) ↔
      (circuit.Assumptions (eval env b) →
        circuit.Spec (eval env b) (eval env (circuit.output b n))) := by
  simp [circuit_norm]

theorem wsubA {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {env : ProverEnvironment F} {circuit : GeneralFormalCircuit F Input Output} {b : Var Input F}
    {n m : ℕ} :
    env.UsesLocalWitnessesCompleteness m ((subcircuitWithAssertion circuit b).operations n) ↔
      (circuit.ProverAssumptions (eval env b) env.data env.hint →
        (circuit.Assumptions (eval env b) env.data →
          circuit.Spec (eval env b) (eval env (circuit.output b n)) env.data) ∧
        circuit.ProverSpec (eval env b) (eval env (circuit.output b n)) env.hint) := by
  simp [circuit_norm]

theorem wassert {Input : TypeMap} [ProvableType Input]
    {env : ProverEnvironment F} {circuit : FormalAssertion F Input} {b : Var Input F} {n m : ℕ} :
    env.UsesLocalWitnessesCompleteness m ((assertion circuit b).operations n) ↔ True := by
  simp [circuit_norm]

end Peel

/-! ### Evaluating the child gadgets' input structures

The peel leaves every child's interface applied to `eval env <struct literal>`.
These push the evaluation through the literal, so the child `Spec`s come out in
the gadget's own wires without `circuit_norm` ever touching a big vector. -/

section EvalInputs
variable {env : Environment (F circomPrime)}

set_option linter.constructorNameAsVariable false in
@[simp] lemma eval_cls (cls : ByteClass.Outputs E) :
    ProvableStruct.eval env cls = evalCls env cls := by
  obtain ⟨b, c⟩ := cls
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := b
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := c
  simp [circuit_norm, evalCls]

set_option linter.constructorNameAsVariable false in
/-- The same, for the `ProvableType` `eval` (the shape the child `Spec`s leave). -/
@[simp] lemma eval_cls' (cls : ByteClass.Outputs E) :
    (eval env cls : ByteClass.Outputs (F circomPrime)) = evalCls env cls := by
  obtain ⟨b, c⟩ := cls
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := b
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := c
  simp [circuit_norm, evalCls]

/-- `Expression.eval` pushed through a four-element vector literal (the main
automaton's `kinds` input). -/
@[simp] lemma eval_kinds_vec (a b c d : E) :
    (eval env #v[a, b, c, d] : Vector (F circomPrime) 4)
      = #v[Expression.eval env a, Expression.eval env b, Expression.eval env c,
           Expression.eval env d] := by
  rw [CircuitType.eval_var_fields]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

@[simp] lemma eval_mulIn (a b : E) :
    (eval env ({ a := a, b := b } : Var Mul.Inputs (F circomPrime)))
      = { a := Expression.eval env a, b := Expression.eval env b } := by
  simp [circuit_norm]

@[simp] lemma eval_oneHotIn (x : E) :
    (eval env ({ x := x } : Var OneHot.Inputs (F circomPrime)))
      = { x := Expression.eval env x } := by
  simp [circuit_norm]

@[simp] lemma eval_subAutoIn (inStr active : E) (cls : ByteClass.Outputs E)
    (sp sn : Vector E nSub) :
    (eval env ({ inStr := inStr, active := active, cls := cls, subPrev := sp,
                 subNext := sn } : Var SubAutomaton.Inputs (F circomPrime)))
      = { inStr := Expression.eval env inStr, active := Expression.eval env active,
          cls := evalCls env cls, subPrev := eval env sp,
          subNext := eval env sn } := by
  simp only [circuit_norm, eval_cls]

@[simp] lemma eval_mainAutoIn (active cq : E) (cls : ByteClass.Outputs E)
    (kinds : Vector E 4) (sp sn : Vector E nSt) :
    (eval env ({ active := active, closeQuote := cq, cls := cls, kinds := kinds,
                 stPrev := sp, stNext := sn } : Var MainAutomaton.Inputs (F circomPrime)))
      = { active := Expression.eval env active, closeQuote := Expression.eval env cq,
          cls := evalCls env cls, kinds := eval env kinds,
          stPrev := eval env sp, stNext := eval env sn } := by
  simp only [circuit_norm, eval_cls]

@[simp] lemma eval_matcherIn (cp emit : E) (kIdxOH : Vector E kIdxMax)
    (mPrev mNext keyStart keyClose stKey active : E) :
    (eval env ({ cp := cp, emit := emit, kIdxOH := kIdxOH, mPrev := mPrev, mNext := mNext,
                 keyStart := keyStart, keyClose := keyClose, stKey := stKey,
                 active := active } : Var Matcher.Inputs (F circomPrime)))
      = { cp := Expression.eval env cp, emit := Expression.eval env emit,
          kIdxOH := eval env kIdxOH, mPrev := Expression.eval env mPrev,
          mNext := Expression.eval env mNext, keyStart := Expression.eval env keyStart,
          keyClose := Expression.eval env keyClose, stKey := Expression.eval env stKey,
          active := Expression.eval env active } := by
  simp [circuit_norm]

@[simp] lemma eval_routeSlotOut (sel ex : E) :
    (eval env ({ sel := sel, exists_ := ex } : Var RouteSlot.Outputs (F circomPrime)))
      = { sel := Expression.eval env sel, exists_ := Expression.eval env ex } := by
  simp [circuit_norm]

@[simp] lemma eval_routeSlotIn {n : ℕ} (claimFlag : E) (ofsOH : Vector E ofsMax)
    (cells : Vector E n) :
    (eval env ({ claimFlag := claimFlag, ofsOH := ofsOH,
                 cells := cells } : Var (RouteSlot.Inputs n) (F circomPrime)))
      = { claimFlag := Expression.eval env claimFlag, ofsOH := eval env ofsOH,
          cells := eval env cells } := by
  simp [circuit_norm]

end EvalInputs

end Step
end Solution.JSONExtract
