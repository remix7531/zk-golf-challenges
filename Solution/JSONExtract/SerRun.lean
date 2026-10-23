import Solution.JSONExtract.SerStep

/-!
# The run of a serialization (`JSONExtract`)

The forward half of the grammar argument: a well-formed `Ser` makes the
automaton accept its bytes, and the read-outs of that run are the slots of its
members.  Everything is assembled from the per-transition lemmas of
`SerStep.lean` by `runL`/`traceL` concatenation.
-/

namespace Solution.JSONExtract

open Model (St Sub Claim Regs Kind nClaims kIdxMax ofsMax)

namespace SerRun

open Model
open Serial
open SerStep
open RunList (runL traceL valsT pMatch pEmit pMinus pTrue fVal)
open Specs.JSON (quote backslash slash lbrace rbrace colon comma minus plus dot
  digit0 digit9 lowerA lowerB lowerE lowerF lowerN lowerR lowerT lowerU upperA upperE upperF
  space tab lf cr backspace formfeed trueLit falseLit nullLit)

/-! ## The key matcher along a key body -/

/-- The key index after `cnt` emitted code points, starting from `i`. -/
def kIdxAfter : ℕ → ℕ → ℕ
  | i, 0 => i
  | i, cnt + 1 => kIdxAfter (min (i + 1) (kIdxMax - 1)) cnt

/-- The matcher flag of claim `k` after the code points `cps`. -/
def mAfter (k : Claim) : Bool → ℕ → List ℕ → Bool
  | f, _, [] => f
  | f, i, cp :: cps => mAfter k (f && decide (cp = nameAt k i)) (min (i + 1) (kIdxMax - 1)) cps

theorem kIdxAfter_eq : ∀ (cnt i : ℕ), i ≤ kIdxMax - 1 →
    kIdxAfter i cnt = min (i + cnt) (kIdxMax - 1) := by
  intro cnt
  induction cnt with
  | zero => intro i hi; simp [kIdxAfter]; omega
  | succ cnt ih =>
    intro i hi
    rw [kIdxAfter, ih _ (by simp only [kIdxMax]; omega)]
    simp only [kIdxMax] at *
    omega

theorem mAfter_false (k : Claim) : ∀ (cps : List ℕ) (i : ℕ), mAfter k false i cps = false := by
  intro cps
  induction cps with
  | nil => intro i; rfl
  | cons c cps ih => intro i; rw [mAfter]; simpa using ih _

theorem mAfter_true_iff (k : Claim) : ∀ (cps : List ℕ) (i : ℕ), i ≤ kIdxMax - 1 →
    (mAfter k true i cps = true ↔
      ∀ j, ∀ _ : j < cps.length, cps[j] = nameAt k (min (i + j) (kIdxMax - 1))) := by
  intro cps
  induction cps with
  | nil => intro i _; simp [mAfter]
  | cons c cps ih =>
    intro i hi
    have hi' : min (i + 1) (kIdxMax - 1) ≤ kIdxMax - 1 := by simp only [kIdxMax]; omega
    rw [mAfter]
    by_cases hc : c = nameAt k i
    · rw [show (true && decide (c = nameAt k i)) = true by simp [hc], ih _ hi']
      constructor
      · intro h j hj
        cases j with
        | zero =>
          simp only [List.getElem_cons_zero, Nat.add_zero]
          rw [Nat.min_eq_left (show i ≤ kIdxMax - 1 from hi)]
          exact hc
        | succ j =>
          have := h j (by simpa using hj)
          simp only [List.getElem_cons_succ]
          rw [this]
          congr 1
          simp only [kIdxMax] at *
          omega
      · intro h j hj
        have := h (j + 1) (by simpa using hj)
        simp only [List.getElem_cons_succ] at this
        rw [this]
        congr 1
        simp only [kIdxMax] at *
        omega
    · rw [show (true && decide (c = nameAt k i)) = false by simp [hc], mAfter_false]
      simp only [Bool.false_eq_true, false_iff, not_forall]
      refine ⟨0, by simp, ?_⟩
      simp only [List.getElem_cons_zero, Nat.add_zero,
        Nat.min_eq_left (show i ≤ kIdxMax - 1 from hi)]
      exact hc

theorem claimName_length_le (k : Claim) : (claimName k).length ≤ 14 := by revert k; decide

theorem match_iff (k : Claim) (cps : List ℕ) :
    (mAfter k true 0 cps && decide (kIdxAfter 0 cps.length = (claimName k).length)) = true
      ↔ cps = claimName k := by
  have hlen := claimName_length_le k
  rw [kIdxAfter_eq _ _ (by simp only [kIdxMax]; omega), Bool.and_eq_true, decide_eq_true_eq,
    Nat.zero_add]
  constructor
  · rintro ⟨hm, hl⟩
    have hcl : cps.length = (claimName k).length := by
      simp only [kIdxMax] at hl; omega
    have := (mAfter_true_iff k cps 0 (by simp only [kIdxMax]; omega)).mp hm
    refine List.ext_getElem hcl fun j h1 h2 => ?_
    have := this j h1
    rw [this, Nat.zero_add, Nat.min_eq_left (by simp only [kIdxMax]; omega),
      nameAt, List.getD_eq_getElem _ _ h2]
  · rintro rfl
    refine ⟨?_, by simp only [kIdxMax]; omega⟩
    rw [mAfter_true_iff k _ 0 (by simp only [kIdxMax]; omega)]
    intro j hj
    rw [Nat.zero_add, Nat.min_eq_left (by simp only [kIdxMax] at *; omega), nameAt,
      List.getD_eq_getElem _ _ hj]

/-! ## The run of a key -/

@[simp] theorem seBytes_nil : seBytes [] = [] := rfl

theorem seBytes_cons (e : SE) (l : List SE) : seBytes (e :: l) = e.bytes ++ seBytes l := by
  simp [seBytes]

@[simp] theorem mcps_nil : mcps [] = [] := rfl

theorem mcps_cons (e : SE) (l : List SE) : mcps (e :: l) = e.mcp :: mcps l := rfl

theorem mcps_length (l : List SE) : (mcps l).length = l.length := by simp [mcps]

theorem key_body_run : ∀ (body : List SE), (∀ e ∈ body, e.WF) → ∀ (i n : ℕ), i ≤ kIdxMax - 1 →
    ∀ mv : Vector Bool nClaims,
      runL (kRegs Sub.PLAIN 0 i mv n) (seBytes body)
          = some (kRegs Sub.PLAIN 0 (kIdxAfter i body.length)
              (Vector.ofFn fun k : Claim => mAfter k mv[k] i (mcps body)) n) ∧
        Quiet (traceL (kRegs Sub.PLAIN 0 i mv n) (seBytes body)) := by
  intro body
  induction body with
  | nil =>
    intro _ i n _ mv
    refine ⟨?_, quiet_nil⟩
    simp only [seBytes_nil, RunList.runL_nil, mcps_nil, List.length_nil, kIdxAfter, mAfter,
      Option.some.injEq]
    rw [ofFn_getElem_self]
  | cons e rest ih =>
    intro hwf i n hi mv
    have hi' : min (i + 1) (kIdxMax - 1) ≤ kIdxMax - 1 := by simp only [kIdxMax]; omega
    obtain ⟨s1, q1⟩ := se_run_key (e := e) (hwf e (List.mem_cons_self ..)) (h := 0) (i := i)
      (n := n) hi (mv := mv)
    obtain ⟨s2, q2⟩ := ih (fun x hx => hwf x (List.mem_cons_of_mem _ hx))
      (min (i + 1) (kIdxMax - 1)) n hi'
      (Vector.ofFn fun k : Claim => mv[k] && decide (e.mcp = nameAt k i))
    constructor
    · rw [seBytes_cons, RunList.runL_append_of s1, s2]
      have hlen : kIdxAfter (min (i + 1) (kIdxMax - 1)) rest.length
          = kIdxAfter i (e :: rest).length := by
        simp only [List.length_cons, kIdxAfter]
      have hvec : (Vector.ofFn fun k : Claim =>
            mAfter k ((Vector.ofFn fun k : Claim => mv[k] && decide (e.mcp = nameAt k i))[k])
              (min (i + 1) (kIdxMax - 1)) (mcps rest))
          = (Vector.ofFn fun k : Claim => mAfter k mv[k] i (mcps (e :: rest))) := by
        refine Vector.ext fun t ht => ?_
        simp only [Vector.getElem_ofFn]
        rw [mcps_cons, mAfter]
        simp
      rw [hlen, hvec]
    · rw [seBytes_cons, RunList.traceL_append s1]
      exact quiet_append q1 q2

/-- The closing quote of a key: the only position where a key match fires. -/
theorem step_closeKey {i n : ℕ} {mv : Vector Bool nClaims} :
    ∃ r', step (kRegs Sub.PLAIN 0 i mv n) quote = some r' ∧
      AtS St.AKEY ((List.finRange nClaims).find? fun k : Claim =>
        (mv[k] && decide (i = (claimName k).length))) n r' ∧
      (∀ k : Claim, pMatch k (kRegs Sub.PLAIN 0 i mv n, quote)
        = (mv[k] && decide (i = (claimName k).length))) ∧
      (∀ k : Claim, pEmit k (kRegs Sub.PLAIN 0 i mv n, quote) = false) ∧
      (∀ k : Claim, pMinus k (kRegs Sub.PLAIN 0 i mv n, quote) = false) ∧
      (∀ k : Claim, pTrue k (kRegs Sub.PLAIN 0 i mv n, quote) = false) := by
  set r : Regs := kRegs Sub.PLAIN 0 i mv n with hr
  have hstK : r.st = St.KEY := rfl
  have hsubr : r.sub = Sub.PLAIN := rfl
  have hstr : inStr r.st = true := rfl
  have e1 : stepSub (inStr r.st) r.sub quote = some Sub.PLAIN := stepSub_plain_quote
  have e2 : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st quote = some St.AKEY := by
    rw [hstK, hsubr]; simpa using stepSt_key_quote (kindOf r.claim)
  have hem : ∀ t : St, (signals r quote t).emit = false := fun t => by
    rw [sig_emit_inStr hstr, hsubr]; decide
  have hve : ∀ t : St, (signals r quote t).vEmit = false := fun t => by
    rw [Step.sig_vEmit, Step.strEmitB, Step.digitEmitB, hem r.st, hstK]
    simp [St.KEY, St.STR, St.PVAL, St.NSIGN, St.NINT]
  have hw := sig_write_of_vEmit (hve St.AKEY)
  have hkcB : Step.keyCloseB r quote = true := by
    rw [Step.keyCloseB, hstK, hsubr]; simp
  have hmatch : ∀ k : Claim, (signals r quote St.AKEY).match_[k]
      = (mv[k] && decide (i = (claimName k).length)) := by
    intro k
    rw [Step.sig_match, hkcB]
    simp only [Bool.true_and]
    rfl
  have hks : (signals r quote St.AKEY).keyStart = false := by
    rw [sig_keyStart]; simp [St.AKEY, St.KEY]
  have hkc : (signals r quote St.AKEY).keyClose = true := by rw [Step.sig_keyClose]; exact hkcB
  refine ⟨mkNext r quote Sub.PLAIN St.AKEY,
    step_eq e1 e2 (by rw [hw]; simp) (by rw [hw]; simp), ⟨rfl, rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [mkNext, hkc, if_true]
    congr 1
    funext k
    exact hmatch k
  · simp only [mkNext, hks, Bool.false_eq_true, if_false, add_zero]; rfl
  · intro k; exact hmatch k
  · intro k; rw [pEmit]; simp [hve r.st]
  · intro k; rw [pMinus, Step.sig_minusFlag]; simp [hstK, St.KEY, St.PVAL]
  · intro k; rw [pTrue, Step.sig_trueDone]; simp [hstK, St.KEY, St.T3]

/-! ## The run of a string value -/

theorem claimCap_le' (k : Claim) : claimCap k ≤ ofsMax - 1 := RunTheory.claimCap_le k

theorem str_body_run : ∀ (body : List SE), (∀ e ∈ body, e.WF) → ∀ (c : Option Claim) (o n : ℕ),
    o ≤ ofsMax - 1 →
    ((kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ k : Claim, c = some k →
      o + body.length ≤ claimCap k) →
    ((kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ e ∈ body, e.mcp < 0x80) →
    runL (sRegs Sub.PLAIN 0 c o n) (seBytes body)
        = some (sRegs Sub.PLAIN 0 c (min (o + body.length) (ofsMax - 1)) n) ∧
      Contrib c 0 (mcps body) 0 0 (traceL (sRegs Sub.PLAIN 0 c o n) (seBytes body)) := by
  intro body
  induction body with
  | nil =>
    intro _ c o n ho _ _
    refine ⟨?_, contrib_of_quiet quiet_nil c⟩
    simp only [seBytes_nil, RunList.runL_nil, List.length_nil, Nat.add_zero,
      Nat.min_eq_left ho]
  | cons e rest ih =>
    intro hwf c o n ho hcap hascii
    obtain ⟨s1, k1⟩ := se_run_str (e := e) (hwf e (List.mem_cons_self ..)) (h := 0) (c := c)
      (o := o) (n := n) ho
      (fun hk k hck => by
        have := hcap hk k hck
        simp only [List.length_cons] at this
        omega)
      (fun hk => hascii hk e (List.mem_cons_self ..))
    obtain ⟨s2, k2⟩ := ih (fun x hx => hwf x (List.mem_cons_of_mem _ hx)) c
      (min (o + 1) (ofsMax - 1)) n (by omega)
      (fun hk k hck => by
        have h1 := hcap hk k hck
        have h2 := claimCap_le' k
        simp only [List.length_cons] at h1
        omega)
      (fun hk x hx => hascii hk x (List.mem_cons_of_mem _ hx))
    constructor
    · rw [seBytes_cons, RunList.runL_append_of s1, s2]
      congr 2
      simp only [List.length_cons]
      omega
    · rw [seBytes_cons, RunList.traceL_append s1]
      have := contrib_append k1 k2
      simpa [mcps_cons] using this

/-- The closing quote of a string value. -/
theorem step_closeStr {c : Option Claim} {o n : ℕ} (ho : o ≤ ofsMax - 1) :
    step (sRegs Sub.PLAIN 0 c o n) quote = some (nRegs St.AVAL c o n) ∧
      Silent (sRegs Sub.PLAIN 0 c o n, quote) := by
  have ho' : o ≤ 128 := by simpa using ho
  set r : Regs := sRegs Sub.PLAIN 0 c o n with hr
  have hstS : r.st = St.STR := rfl
  have hsubr : r.sub = Sub.PLAIN := rfl
  have hstr : inStr r.st = true := rfl
  have e1 : stepSub (inStr r.st) r.sub quote = some Sub.PLAIN := stepSub_plain_quote
  have e2 : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st quote = some St.AVAL := rfl
  have hem : ∀ t : St, (signals r quote t).emit = false := fun t => by
    rw [sig_emit_inStr hstr, hsubr]; decide
  have hve : ∀ t : St, (signals r quote t).vEmit = false := fun t => by
    rw [Step.sig_vEmit, Step.strEmitB, Step.digitEmitB, hem r.st, hstS]
    simp [St.STR, St.PVAL, St.NSIGN, St.NINT]
  have hw := sig_write_of_vEmit (hve St.AVAL)
  have hks : (signals r quote St.AVAL).keyStart = false := by
    rw [sig_keyStart]; simp [St.AVAL, St.KEY]
  have hkc : (signals r quote St.AVAL).keyClose = false := by
    rw [Step.sig_keyClose, Step.keyCloseB, hstS]; simp [St.STR, St.KEY]
  constructor
  · rw [step_eq e1 e2 (by rw [hw]; simp) (by rw [hw]; simp)]
    congr 1
    simp only [mkNext, nRegs, Regs.mk.injEq, hks, hkc, hve, hstS, hsubr,
      Bool.false_eq_true, if_false]
    and_intros <;>
      first
        | trivial
        | (exact Vector.ext fun t ht => by simp [St.STR, St.KEY])
        | (rw [if_pos (by decide)]; show min o 128 = o; omega)
        | simp [Sub.PLAIN, Sub.H1, Sub.H2, Sub.H3]
  · exact silent_sig0
      (fun k => by rw [Step.sig_match, Step.keyCloseB, hstS]; simp [St.STR, St.KEY])
      (hve r.st)
      (by rw [Step.sig_minusFlag, hstS]; simp [St.STR, St.PVAL])
      (by rw [Step.sig_trueDone, hstS]; simp [St.STR, St.T3])

/-! ## Composing segments -/

theorem runCC {r r1 rf : Regs} {L1 L2 : List ℕ} {c : Option Claim}
    {m1 m2 : ℕ} {v1 v2 : List ℕ} {s1 s2 t1 t2 : ℕ}
    (h1 : runL r L1 = some r1) (k1 : Contrib c m1 v1 s1 t1 (traceL r L1))
    (h2 : runL r1 L2 = some rf) (k2 : Contrib c m2 v2 s2 t2 (traceL r1 L2)) :
    runL r (L1 ++ L2) = some rf ∧
      Contrib c (m1 + m2) (v1 ++ v2) (s1 + s2) (t1 + t2) (traceL r (L1 ++ L2)) := by
  refine ⟨by rw [RunList.runL_append_of h1]; exact h2, ?_⟩
  rw [RunList.traceL_append h1]
  exact contrib_append k1 k2

theorem runQQ {r r1 rf : Regs} {L1 L2 : List ℕ}
    (h1 : runL r L1 = some r1) (k1 : Quiet (traceL r L1))
    (h2 : runL r1 L2 = some rf) (k2 : Quiet (traceL r1 L2)) :
    runL r (L1 ++ L2) = some rf ∧ Quiet (traceL r (L1 ++ L2)) := by
  refine ⟨by rw [RunList.runL_append_of h1]; exact h2, ?_⟩
  rw [RunList.traceL_append h1]
  exact quiet_append k1 k2

theorem contrib_single_of_silent {r : Regs} {b : ℕ} (h : Silent (r, b)) (c : Option Claim) :
    Contrib c 0 [] 0 0 (traceL r [b]) := by
  rw [RunList.traceL_single]
  exact contrib_of_quiet (quiet_single h) c

/-! ## Normalised steps outside a string -/

theorem dEmit_digit {s : St} {b : ℕ} (h : dEmit s b = true) : Model.isDigit b = true := by
  rw [dEmit, Bool.and_eq_true] at h; exact h.1

theorem dEmit_state {s : St} {b : ℕ} (h : dEmit s b = true) :
    s = St.PVAL ∨ s = St.NSIGN ∨ s = St.NINT := by
  rw [dEmit, Bool.and_eq_true] at h
  have := h.2
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  tauto

theorem isDigit_ne_minus {b : ℕ} (h : Model.isDigit b = true) : (b == minus) = false := by
  simp only [Model.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [beq_eq_false_iff_ne, ne_eq]
  show b ≠ 0x2D
  have : (0x30 : ℕ) ≤ b := h.1
  omega

theorem nstepQ {s s' : St} {c : Option Claim} {o o' n b : ℕ}
    (hnstr : inStr s = false) (hs'k : s' ≠ St.KEY)
    (hst : stepSt (kindOf c) true s b = some s')
    (hd : dEmit s b = false) (hmi : (decide (s = St.PVAL) && (b == minus)) = false)
    (htr : (decide (s = St.T3) && (b == lowerE)) = false)
    (ho : min (if Step.inValP s = true then o else 0) (ofsMax - 1) = o') :
    step (nRegs s c o n) b = some (nRegs s' c o' n) ∧ Silent (nRegs s c o n, b) := by
  obtain ⟨hstep, hm, hem, _, hmi', htr'⟩ := step_nRegs hnstr hs'k hst (by rw [hd]; simp)
  refine ⟨?_, hm, fun k => by rw [hem k, hd]; simp, fun k => by rw [hmi' k, hmi]; simp,
    fun k => by rw [htr' k, htr]; simp⟩
  rw [hstep, hd]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero]
  rw [ho]

theorem nstepE {s s' : St} {c : Option Claim} {o o' n b : ℕ}
    (hnstr : inStr s = false) (hs'k : s' ≠ St.KEY)
    (hst : stepSt (kindOf c) true s b = some s')
    (hd : dEmit s b = true)
    (hcap : (kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ k : Claim, c = some k →
      o < claimCap k)
    (ho : min ((if Step.inValP s = true then o else 0) + 1) (ofsMax - 1) = o') :
    step (nRegs s c o n) b = some (nRegs s' c o' n) ∧
      Contrib c 0 [b - digit0] 0 0 (traceL (nRegs s c o n) [b]) := by
  obtain ⟨hstep, hk⟩ := contrib_nstep hnstr hs'k hst (fun _ => hcap)
  have hmi : (decide (s = St.PVAL) && (b == minus)) = false := by
    rw [isDigit_ne_minus (dEmit_digit hd)]; simp
  have htr : (decide (s = St.T3) && (b == lowerE)) = false := by
    rcases dEmit_state hd with h | h | h <;> rw [h] <;> simp [St.PVAL, St.NSIGN, St.NINT, St.T3]
  refine ⟨?_, ?_⟩
  · rw [hstep, hd]; simp only [if_true]; rw [ho]
  · rw [hd, hmi, htr] at hk; simpa using hk

theorem nstepM {c : Option Claim} {o n : ℕ}
    (hst : stepSt (kindOf c) true St.PVAL minus = some St.NSIGN) :
    step (nRegs St.PVAL c o n) minus = some (nRegs St.NSIGN c 0 n) ∧
      Contrib c 0 [] 1 0 (traceL (nRegs St.PVAL c o n) [minus]) := by
  obtain ⟨hstep, hk⟩ := contrib_nstep (s := St.PVAL) (s' := St.NSIGN) (by decide) (by decide)
    hst (by intro h; exact absurd h (by decide))
  have hd : dEmit St.PVAL minus = false := by decide
  refine ⟨?_, ?_⟩
  · rw [hstep, hd]; simp only [Bool.false_eq_true, if_false, Nat.add_zero]
    rw [if_neg (by decide)]
    rfl
  · rw [hd] at hk
    simpa using hk

theorem nstepT {c : Option Claim} {o n : ℕ} (ho : o ≤ ofsMax - 1) :
    step (nRegs St.T3 c o n) lowerE = some (nRegs St.AVAL c o n) ∧
      Contrib c 0 [] 0 1 (traceL (nRegs St.T3 c o n) [lowerE]) := by
  obtain ⟨hstep, hk⟩ := contrib_nstep (s := St.T3) (s' := St.AVAL) (c := c) (o := o) (n := n)
    (b := lowerE) (by decide) (by decide) rfl (by intro h; exact absurd h (by decide))
  have hd : dEmit St.T3 lowerE = false := by decide
  have ho' : o ≤ 128 := by simpa using ho
  refine ⟨?_, ?_⟩
  · rw [hstep, hd]; simp only [Bool.false_eq_true, if_false, Nat.add_zero]
    rw [if_pos (by decide)]
    rw [show min o (ofsMax - 1) = o from Nat.min_eq_left ho]
  · rw [hd] at hk
    simpa using hk

/-! ## Equations of the number states -/

theorem stepSt_pval_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.PVAL b =
      (if Model.isWs b = true then some St.PVAL
       else if ((b == quote) && (decide (kind = Kind.str) || decide (kind = Kind.unk))) = true then
         some St.STR
       else if ((b == minus) && (decide (kind = Kind.int) || decide (kind = Kind.unk))) = true then
         some St.NSIGN
       else if ((b == digit0) && (decide (kind = Kind.int) || decide (kind = Kind.unk))) = true then
         some St.NZERO
       else if (Model.isDigitNz b && (decide (kind = Kind.int) || decide (kind = Kind.unk)))
           = true then some St.NINT
       else if ((b == lowerT) && (decide (kind = Kind.bool) || decide (kind = Kind.unk)))
           = true then some St.T1
       else if ((b == lowerF) && (decide (kind = Kind.bool) || decide (kind = Kind.unk)))
           = true then some St.F1
       else if ((b == lowerN) && decide (kind = Kind.unk)) = true then some St.N1
       else none) := rfl

theorem stepSt_nsign_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.NSIGN b =
      (if (b == digit0) = true then some St.NZERO
       else if Model.isDigitNz b = true then some St.NINT else none) := rfl

theorem stepSt_nzero_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.NZERO b =
      (if ((b == dot) && decide (kind = Kind.unk)) = true then some St.NDOT
       else if (Model.isExpLetter b && decide (kind = Kind.unk)) = true then some St.NE
       else afterValue b) := rfl

theorem stepSt_nint_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.NINT b =
      (if Model.isDigit b = true then some St.NINT
       else if ((b == dot) && decide (kind = Kind.unk)) = true then some St.NDOT
       else if (Model.isExpLetter b && decide (kind = Kind.unk)) = true then some St.NE
       else afterValue b) := rfl

theorem stepSt_ndot_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.NDOT b = (if Model.isDigit b = true then some St.NFRAC else none) := rfl

theorem stepSt_nfrac_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.NFRAC b =
      (if Model.isDigit b = true then some St.NFRAC
       else if Model.isExpLetter b = true then some St.NE else afterValue b) := rfl

theorem stepSt_ne_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.NE b =
      (if Model.isSign b = true then some St.NESIGN
       else if Model.isDigit b = true then some St.NEXP else none) := rfl

theorem stepSt_nesign_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.NESIGN b = (if Model.isDigit b = true then some St.NEXP else none) := rfl

theorem stepSt_nexp_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.NEXP b =
      (if Model.isDigit b = true then some St.NEXP else afterValue b) := rfl

/-! ## Digit arithmetic -/

theorem isDigit_add {x : ℕ} (h : x ≤ 9) : Model.isDigit (x + digit0) = true := by
  simp only [Model.isDigit, Bool.and_eq_true, decide_eq_true_eq]
  show (0x30 : ℕ) ≤ x + 0x30 ∧ x + 0x30 ≤ 0x39
  omega

theorem isDigitNz_add {x : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ 9) : Model.isDigitNz (x + digit0) = true := by
  simp only [Model.isDigitNz, Bool.and_eq_true, decide_eq_true_eq]
  show (0x30 : ℕ) < x + 0x30 ∧ x + 0x30 ≤ 0x39
  omega

theorem add_sub_digit0 (x : ℕ) : x + digit0 - digit0 = x := by
  show x + 0x30 - 0x30 = x
  omega

theorem digit_ne_dot {x : ℕ} (h : x ≤ 9) : ((x + digit0) == dot) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  show x + 0x30 ≠ 0x2E
  omega

theorem digit_not_exp {x : ℕ} (h : x ≤ 9) : Model.isExpLetter (x + digit0) = false := by
  simp only [Model.isExpLetter, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  constructor <;> [show x + 0x30 ≠ 0x65; show x + 0x30 ≠ 0x45] <;> omega

theorem dEmit_of_digit {s : St} {b : ℕ} (hd : Model.isDigit b = true)
    (hs : s = St.PVAL ∨ s = St.NSIGN ∨ s = St.NINT) : dEmit s b = true := by
  rw [dEmit, hd]
  rcases hs with rfl | rfl | rfl <;> simp [St.PVAL, St.NSIGN, St.NINT]

theorem dEmit_of_notDigit {s : St} {b : ℕ} (h : Model.isDigit b = false) : dEmit s b = false := by
  rw [dEmit, h]; simp

theorem dEmit_quiet {s : St} {b : ℕ} (hs : s = St.NZERO ∨ s = St.NDOT ∨ s = St.NFRAC ∨
    s = St.NE ∨ s = St.NESIGN ∨ s = St.NEXP ∨ s = St.T1 ∨ s = St.T2 ∨ s = St.T3 ∨
    s = St.F1 ∨ s = St.F2 ∨ s = St.F3 ∨ s = St.F4 ∨ s = St.N1 ∨ s = St.N2 ∨ s = St.N3) :
    dEmit s b = false := by
  rw [dEmit]
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [St.PVAL, St.NSIGN, St.NINT, St.NZERO, St.NDOT, St.NFRAC, St.NE, St.NESIGN, St.NEXP,
      St.T1, St.T2, St.T3, St.F1, St.F2, St.F3, St.F4, St.N1, St.N2, St.N3]

/-! ## Digit runs -/

theorem nint_digits_run : ∀ (ds : List ℕ), (∀ x ∈ ds, x ≤ 9) → ∀ (c : Option Claim) (o n : ℕ),
    o ≤ ofsMax - 1 →
    ((kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ k : Claim, c = some k →
      o + ds.length ≤ claimCap k) →
    runL (nRegs St.NINT c o n) (ds.map (· + digit0))
        = some (nRegs St.NINT c (min (o + ds.length) (ofsMax - 1)) n) ∧
      Contrib c 0 ds 0 0 (traceL (nRegs St.NINT c o n) (ds.map (· + digit0))) := by
  intro ds
  induction ds with
  | nil =>
    intro _ c o n ho _
    refine ⟨?_, contrib_of_quiet quiet_nil c⟩
    simp only [List.map_nil, RunList.runL_nil, List.length_nil, Nat.add_zero,
      Nat.min_eq_left ho]
  | cons x ds ih =>
    intro hx c o n ho hcap
    have hx9 : x ≤ 9 := hx x (List.mem_cons_self ..)
    have hd : Model.isDigit (x + digit0) = true := isDigit_add hx9
    obtain ⟨s1, k1⟩ := nstepE (s := St.NINT) (s' := St.NINT) (c := c) (o := o) (n := n)
      (by decide) (by decide) (by rw [stepSt_nint_eq, if_pos hd])
      (dEmit_of_digit hd (Or.inr (Or.inr rfl)))
      (fun hk k hck => by
        have := hcap hk k hck
        simp only [List.length_cons] at this
        omega)
      rfl
    obtain ⟨s2, k2⟩ := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) c
      (min ((if Step.inValP St.NINT = true then o else 0) + 1) (ofsMax - 1)) n (by omega)
      (fun hk k hck => by
        have h1 := hcap hk k hck
        have h2 := claimCap_le' k
        simp only [List.length_cons] at h1
        rw [if_pos (by decide)]
        simp only [ofsMax] at *
        omega)
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, show (x + digit0) :: ds.map (· + digit0)
        = [x + digit0] ++ ds.map (· + digit0) from rfl, RunList.runL_append_of
        (by rw [RunList.runL_single]; exact s1), s2]
      congr 2
      rw [if_pos (by decide)]
      simp only [List.length_cons, ofsMax] at *
      omega
    · rw [List.map_cons, show (x + digit0) :: ds.map (· + digit0)
        = [x + digit0] ++ ds.map (· + digit0) from rfl,
        RunList.traceL_append (by rw [RunList.runL_single]; exact s1)]
      have := contrib_append k1 k2
      rw [add_sub_digit0] at this
      simpa using this

theorem quiet_digits_run {s : St} (hs : s = St.NFRAC ∨ s = St.NEXP) :
    ∀ (ds : List ℕ), (∀ x ∈ ds, x ≤ 9) → ∀ (c : Option Claim) (o n : ℕ), o ≤ ofsMax - 1 →
      runL (nRegs s c o n) (ds.map (· + digit0)) = some (nRegs s c o n) ∧
        Quiet (traceL (nRegs s c o n) (ds.map (· + digit0))) := by
  intro ds
  induction ds with
  | nil => intro _ c o n _; exact ⟨rfl, quiet_nil⟩
  | cons x ds ih =>
    intro hx c o n ho
    have hx9 : x ≤ 9 := hx x (List.mem_cons_self ..)
    have hd : Model.isDigit (x + digit0) = true := isDigit_add hx9
    have hstep : stepSt (kindOf c) true s (x + digit0) = some s := by
      rcases hs with rfl | rfl
      · rw [stepSt_nfrac_eq, if_pos hd]
      · rw [stepSt_nexp_eq, if_pos hd]
    obtain ⟨s1, q1⟩ := nstepQ (s := s) (s' := s) (c := c) (o := o) (o' := o) (n := n)
      (by rcases hs with rfl | rfl <;> decide) (by rcases hs with rfl | rfl <;> decide)
      hstep (dEmit_quiet (by rcases hs with rfl | rfl <;> simp))
      (by rcases hs with rfl | rfl <;> simp [St.NFRAC, St.NEXP, St.PVAL])
      (by rcases hs with rfl | rfl <;> simp [St.NFRAC, St.NEXP, St.T3])
      (by rw [if_pos (by rcases hs with rfl | rfl <;> decide)]; exact Nat.min_eq_left ho)
    obtain ⟨s2, q2⟩ := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) c o n ho
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, show (x + digit0) :: ds.map (· + digit0)
        = [x + digit0] ++ ds.map (· + digit0) from rfl, RunList.runL_append_of
        (by rw [RunList.runL_single]; exact s1), s2]
    · rw [List.map_cons, show (x + digit0) :: ds.map (· + digit0)
        = [x + digit0] ++ ds.map (· + digit0) from rfl,
        RunList.traceL_append (by rw [RunList.runL_single]; exact s1)]
      refine quiet_append ?_ q2
      rw [RunList.traceL_single]
      exact quiet_single q1

/-! ## The fractional and exponent parts -/

def fracB (nm : SNum) : List ℕ := if nm.frac = [] then [] else dot :: nm.frac.map (· + digit0)
def expB (nm : SNum) : List ℕ := (nm.exp.map SExp.bytes).getD []

theorem SNum_bytes_eq (nm : SNum) :
    nm.bytes = (if nm.neg then [minus] else [])
      ++ (nm.ints.map (· + digit0) ++ (fracB nm ++ expB nm)) := by
  rw [SNum.bytes, fracB, expB]
  cases nm.exp <;> simp [List.append_assoc]

theorem inValP_num {s : St} (hs : s = St.NZERO ∨ s = St.NINT ∨ s = St.NFRAC ∨ s = St.NE ∨
    s = St.NESIGN ∨ s = St.NEXP ∨ s = St.NDOT) : Step.inValP s = true := by
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

set_option maxHeartbeats 2000000 in
theorem exp_run {s2 : St} (hs2 : s2 = St.NZERO ∨ s2 = St.NINT ∨ s2 = St.NFRAC)
    {e : SExp} (hl : e.letter = lowerE ∨ e.letter = upperE)
    (hsg : match e.sign with | none => True | some sg => sg = plus ∨ sg = minus)
    (hne : e.digits ≠ []) (hdg : ∀ x ∈ e.digits, x ≤ 9)
    {c : Option Claim} {o n : ℕ} (ho : o ≤ ofsMax - 1)
    (hunk : s2 = St.NZERO ∨ s2 = St.NINT → kindOf c = Kind.unk) :
    runL (nRegs s2 c o n) e.bytes = some (nRegs St.NEXP c o n) ∧
      Quiet (traceL (nRegs s2 c o n) e.bytes) := by
  have hletExp : Model.isExpLetter e.letter = true := by
    rcases hl with h | h <;> rw [h] <;> decide
  have hletNotDigit : Model.isDigit e.letter = false := by
    rcases hl with h | h <;> rw [h] <;> decide
  have hletNotDot : (e.letter == dot) = false := by
    rcases hl with h | h <;> rw [h] <;> decide
  have hletNotWs : Model.isWs e.letter = false := by
    rcases hl with h | h <;> rw [h] <;> decide
  -- step 1: the exponent letter
  have hstep1 : stepSt (kindOf c) true s2 e.letter = some St.NE := by
    rcases hs2 with rfl | rfl | rfl
    · rw [stepSt_nzero_eq, if_neg (by simp [hletNotDot]), if_pos (by simp [hletExp,
        hunk (Or.inl rfl)])]
    · rw [stepSt_nint_eq, if_neg (by simp [hletNotDigit]), if_neg (by simp [hletNotDot]),
        if_pos (by simp [hletExp, hunk (Or.inr rfl)])]
    · rw [stepSt_nfrac_eq, if_neg (by simp [hletNotDigit]), if_pos hletExp]
  obtain ⟨s1, q1⟩ := nstepQ (s := s2) (s' := St.NE) (c := c) (o := o) (o' := o) (n := n)
    (by rcases hs2 with rfl|rfl|rfl <;> decide) (by decide) hstep1
    (dEmit_of_notDigit hletNotDigit)
    (by rcases hs2 with rfl|rfl|rfl <;> simp [St.NZERO, St.NINT, St.NFRAC, St.PVAL])
    (by rcases hs2 with rfl|rfl|rfl <;> simp [St.NZERO, St.NINT, St.NFRAC, St.T3])
    (by rw [if_pos (inValP_num (by rcases hs2 with rfl|rfl|rfl <;> tauto))]
        exact Nat.min_eq_left ho)
  -- step 2: the optional sign, then the digits
  obtain ⟨d, ds, hds⟩ : ∃ d ds, e.digits = d :: ds := by
    cases hx : e.digits with
    | nil => exact absurd hx hne
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hd9 : d ≤ 9 := hdg d (by rw [hds]; exact List.mem_cons_self ..)
  have hdsd : ∀ x ∈ ds, x ≤ 9 := fun x hx => hdg x (by rw [hds]; exact List.mem_cons_of_mem _ hx)
  have hdig : Model.isDigit (d + digit0) = true := isDigit_add hd9
  have hnotsign : Model.isSign (d + digit0) = false := by
    simp only [Model.isSign, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    constructor <;> [show d + 0x30 ≠ 0x2B; show d + 0x30 ≠ 0x2D] <;> omega
  have hrest : ∀ (s : St), (s = St.NE ∨ s = St.NESIGN) →
      runL (nRegs s c o n) ((d :: ds).map (· + digit0)) = some (nRegs St.NEXP c o n) ∧
        Quiet (traceL (nRegs s c o n) ((d :: ds).map (· + digit0))) := by
    intro s hs
    have hstep : stepSt (kindOf c) true s (d + digit0) = some St.NEXP := by
      rcases hs with rfl | rfl
      · rw [stepSt_ne_eq, if_neg (by simp [hnotsign]), if_pos hdig]
      · rw [stepSt_nesign_eq, if_pos hdig]
    obtain ⟨sa, qa⟩ := nstepQ (s := s) (s' := St.NEXP) (c := c) (o := o) (o' := o) (n := n)
      (by rcases hs with rfl|rfl <;> decide) (by decide) hstep
      (dEmit_quiet (by rcases hs with rfl|rfl <;> simp))
      (by rcases hs with rfl|rfl <;> simp [St.NE, St.NESIGN, St.PVAL])
      (by rcases hs with rfl|rfl <;> simp [St.NE, St.NESIGN, St.T3])
      (by rw [if_pos (inValP_num (by rcases hs with rfl|rfl <;> tauto))]
          exact Nat.min_eq_left ho)
    obtain ⟨sb, qb⟩ := quiet_digits_run (s := St.NEXP) (Or.inr rfl) ds hdsd c o n ho
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, show (d + digit0) :: ds.map (· + digit0)
        = [d + digit0] ++ ds.map (· + digit0) from rfl,
        RunList.runL_append_of (by rw [RunList.runL_single]; exact sa), sb]
    · rw [List.map_cons, show (d + digit0) :: ds.map (· + digit0)
        = [d + digit0] ++ ds.map (· + digit0) from rfl,
        RunList.traceL_append (by rw [RunList.runL_single]; exact sa)]
      refine quiet_append ?_ qb
      rw [RunList.traceL_single]
      exact quiet_single qa
  rw [SExp.bytes, hds]
  cases hsn : e.sign with
  | none =>
    simp only [List.nil_append]
    obtain ⟨sb, qb⟩ := hrest St.NE (Or.inl rfl)
    refine ⟨?_, ?_⟩
    · rw [show e.letter :: ((d :: ds).map (· + digit0))
        = [e.letter] ++ ((d :: ds).map (· + digit0)) from rfl,
        RunList.runL_append_of (by rw [RunList.runL_single]; exact s1), sb]
    · rw [show e.letter :: ((d :: ds).map (· + digit0))
        = [e.letter] ++ ((d :: ds).map (· + digit0)) from rfl,
        RunList.traceL_append (by rw [RunList.runL_single]; exact s1)]
      refine quiet_append ?_ qb
      rw [RunList.traceL_single]
      exact quiet_single q1
  | some sg =>
    have hsg' : sg = plus ∨ sg = minus := by rw [hsn] at hsg; exact hsg
    have hsgn : Model.isSign sg = true := by rcases hsg' with rfl | rfl <;> decide
    obtain ⟨sc, qc⟩ := nstepQ (s := St.NE) (s' := St.NESIGN) (c := c) (o := o) (o' := o) (n := n)
      (by decide) (by decide) (by rw [stepSt_ne_eq, if_pos hsgn])
      (dEmit_of_notDigit (by rcases hsg' with rfl|rfl <;> decide))
      (by rcases hsg' with rfl|rfl <;> simp [St.NE, St.PVAL])
      (by rcases hsg' with rfl|rfl <;> simp [St.NE, St.T3])
      (by rw [if_pos (by decide)]; exact Nat.min_eq_left ho)
    obtain ⟨sb, qb⟩ := hrest St.NESIGN (Or.inr rfl)
    simp only [List.cons_append, List.nil_append]
    refine ⟨?_, ?_⟩
    · rw [show e.letter :: sg :: ((d :: ds).map (· + digit0))
        = [e.letter] ++ ([sg] ++ ((d :: ds).map (· + digit0))) from rfl,
        RunList.runL_append_of (by rw [RunList.runL_single]; exact s1),
        RunList.runL_append_of (by rw [RunList.runL_single]; exact sc), sb]
    · rw [show e.letter :: sg :: ((d :: ds).map (· + digit0))
        = [e.letter] ++ ([sg] ++ ((d :: ds).map (· + digit0))) from rfl,
        RunList.traceL_append (by rw [RunList.runL_single]; exact s1),
        RunList.traceL_append (by rw [RunList.runL_single]; exact sc)]
      refine quiet_append ?_ (quiet_append ?_ qb)
      · rw [RunList.traceL_single]; exact quiet_single q1
      · rw [RunList.traceL_single]; exact quiet_single qc

theorem frac_run {s1 : St} (hs1 : s1 = St.NZERO ∨ s1 = St.NINT) {frac : List ℕ}
    (hne : frac ≠ []) (hdg : ∀ x ∈ frac, x ≤ 9) {c : Option Claim} {o n : ℕ}
    (ho : o ≤ ofsMax - 1) (hunk : kindOf c = Kind.unk) :
    runL (nRegs s1 c o n) (dot :: frac.map (· + digit0)) = some (nRegs St.NFRAC c o n) ∧
      Quiet (traceL (nRegs s1 c o n) (dot :: frac.map (· + digit0))) := by
  obtain ⟨d, ds, hds⟩ : ∃ d ds, frac = d :: ds := by
    cases hx : frac with
    | nil => exact absurd hx hne
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hd9 : d ≤ 9 := hdg d (by rw [hds]; exact List.mem_cons_self ..)
  have hdsd : ∀ x ∈ ds, x ≤ 9 := fun x hx => hdg x (by rw [hds]; exact List.mem_cons_of_mem _ hx)
  have hdig : Model.isDigit (d + digit0) = true := isDigit_add hd9
  have hstep1 : stepSt (kindOf c) true s1 dot = some St.NDOT := by
    rcases hs1 with rfl | rfl
    · rw [stepSt_nzero_eq, if_pos (by simp [hunk])]
    · rw [stepSt_nint_eq, if_neg (by decide), if_pos (by simp [hunk])]
  obtain ⟨sa, qa⟩ := nstepQ (s := s1) (s' := St.NDOT) (c := c) (o := o) (o' := o) (n := n)
    (by rcases hs1 with rfl|rfl <;> decide) (by decide) hstep1
    (dEmit_of_notDigit (by decide))
    (by rcases hs1 with rfl|rfl <;> simp [St.NZERO, St.NINT, St.PVAL])
    (by rcases hs1 with rfl|rfl <;> simp [St.NZERO, St.NINT, St.T3])
    (by rw [if_pos (inValP_num (by rcases hs1 with rfl|rfl <;> tauto))]
        exact Nat.min_eq_left ho)
  obtain ⟨sb, qb⟩ := nstepQ (s := St.NDOT) (s' := St.NFRAC) (c := c) (o := o) (o' := o) (n := n)
    (by decide) (by decide) (by rw [stepSt_ndot_eq, if_pos hdig])
    (dEmit_quiet (by simp)) (by simp [St.NDOT, St.PVAL]) (by simp [St.NDOT, St.T3])
    (by rw [if_pos (by decide)]; exact Nat.min_eq_left ho)
  obtain ⟨sc, qc⟩ := quiet_digits_run (s := St.NFRAC) (Or.inl rfl) ds hdsd c o n ho
  rw [hds]
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, show dot :: ((d + digit0) :: ds.map (· + digit0))
      = [dot] ++ ([d + digit0] ++ ds.map (· + digit0)) from rfl,
      RunList.runL_append_of (by rw [RunList.runL_single]; exact sa),
      RunList.runL_append_of (by rw [RunList.runL_single]; exact sb), sc]
  · rw [List.map_cons, show dot :: ((d + digit0) :: ds.map (· + digit0))
      = [dot] ++ ([d + digit0] ++ ds.map (· + digit0)) from rfl,
      RunList.traceL_append (by rw [RunList.runL_single]; exact sa),
      RunList.traceL_append (by rw [RunList.runL_single]; exact sb)]
    refine quiet_append ?_ (quiet_append ?_ qc)
    · rw [RunList.traceL_single]; exact quiet_single qa
    · rw [RunList.traceL_single]; exact quiet_single qb

/-! ## Value-start edges -/

theorem isDigitNz_bounds {b : ℕ} (h : Model.isDigitNz b = true) : 0x30 < b ∧ b ≤ 0x39 := by
  simpa only [Model.isDigitNz, Bool.and_eq_true, decide_eq_true_eq] using h

theorem stepSt_pval_quote {kind : Kind} (h : kind = Kind.str ∨ kind = Kind.unk) :
    stepSt kind true St.PVAL quote = some St.STR := by rcases h with rfl | rfl <;> rfl

theorem stepSt_pval_minus {kind : Kind} (h : kind = Kind.int ∨ kind = Kind.unk) (sp : Bool) :
    stepSt kind sp St.PVAL minus = some St.NSIGN := by rcases h with rfl | rfl <;> rfl

theorem stepSt_pval_digit0 {kind : Kind} (h : kind = Kind.int ∨ kind = Kind.unk) (sp : Bool) :
    stepSt kind sp St.PVAL digit0 = some St.NZERO := by rcases h with rfl | rfl <;> rfl

theorem stepSt_pval_t {kind : Kind} (h : kind = Kind.bool ∨ kind = Kind.unk) (sp : Bool) :
    stepSt kind sp St.PVAL lowerT = some St.T1 := by rcases h with rfl | rfl <;> rfl

theorem stepSt_pval_f {kind : Kind} (h : kind = Kind.bool ∨ kind = Kind.unk) (sp : Bool) :
    stepSt kind sp St.PVAL lowerF = some St.F1 := by rcases h with rfl | rfl <;> rfl

theorem stepSt_pval_n {kind : Kind} (h : kind = Kind.unk) (sp : Bool) :
    stepSt kind sp St.PVAL lowerN = some St.N1 := by rw [h]; rfl

theorem stepSt_pval_dnz {kind : Kind} (h : kind = Kind.int ∨ kind = Kind.unk) (sp : Bool)
    {b : ℕ} (hb : Model.isDigitNz b = true) : stepSt kind sp St.PVAL b = some St.NINT := by
  obtain ⟨hlo, hhi⟩ := isDigitNz_bounds hb
  have hnws : Model.isWs b = false := by
    simp only [Model.isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
      [show b ≠ 0x20; show b ≠ 0x09; show b ≠ 0x0A; show b ≠ 0x0D] <;> omega
  have hnq : (b == quote) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x22; omega
  have hnm : (b == minus) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x2D; omega
  have hn0 : (b == digit0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x30; omega
  rw [stepSt_pval_eq, if_neg (by simp [hnws]), if_neg (by simp [hnq]), if_neg (by simp [hnm]),
    if_neg (by simp [hn0]), if_pos (by rcases h with rfl | rfl <;> simp [hb])]

theorem stepSt_nsign_digit0 (kind : Kind) (sp : Bool) :
    stepSt kind sp St.NSIGN digit0 = some St.NZERO := rfl

theorem stepSt_nsign_dnz (kind : Kind) (sp : Bool) {b : ℕ} (hb : Model.isDigitNz b = true) :
    stepSt kind sp St.NSIGN b = some St.NINT := by
  obtain ⟨hlo, hhi⟩ := isDigitNz_bounds hb
  have hn0 : (b == digit0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x30; omega
  rw [stepSt_nsign_eq, if_neg (by simp [hn0]), if_pos hb]

/-! ## Quiet steps inside a value -/

theorem dEmit_off {s : St} (h1 : s ≠ St.PVAL) (h2 : s ≠ St.NSIGN) (h3 : s ≠ St.NINT) (b : ℕ) :
    dEmit s b = false := by simp [dEmit, h1, h2, h3]

theorem nstepV {s s' : St} {c : Option Claim} {o n b : ℕ}
    (h1 : inStr s = false) (hd : dEmit s b = false)
    (hmi : (decide (s = St.PVAL) && (b == minus)) = false)
    (htr : (decide (s = St.T3) && (b == lowerE)) = false)
    (hval : Step.inValP s = true) (ho : o ≤ ofsMax - 1)
    (hs'k : s' ≠ St.KEY) (hst : stepSt (kindOf c) true s b = some s') :
    step (nRegs s c o n) b = some (nRegs s' c o n) ∧ Silent (nRegs s c o n, b) :=
  nstepQ h1 hs'k hst hd hmi htr (by rw [if_pos hval]; exact Nat.min_eq_left ho)

theorem runQ1 {r r' : Regs} {b : ℕ} (h : step r b = some r' ∧ Silent (r, b)) :
    runL r [b] = some r' ∧ Quiet (traceL r [b]) := by
  refine ⟨by rw [RunList.runL_single]; exact h.1, ?_⟩
  rw [RunList.traceL_single]; exact quiet_single h.2

theorem runC1 {r r' : Regs} {b : ℕ} {c : Option Claim} {m : ℕ} {vs : List ℕ} {sg tr : ℕ}
    (h : step r b = some r' ∧ Contrib c m vs sg tr (traceL r [b])) :
    runL r [b] = some r' ∧ Contrib c m vs sg tr (traceL r [b]) :=
  ⟨by rw [RunList.runL_single]; exact h.1, h.2⟩

/-! ## The integer part of a number -/

theorem ints_run {s0 : St} (hs0 : s0 = St.PVAL ∨ s0 = St.NSIGN) {ints : List ℕ}
    (hwf : ints = [0] ∨ (∃ d ds, ints = d :: ds ∧ 1 ≤ d ∧ d ≤ 9 ∧ ∀ x ∈ ds, x ≤ 9))
    {c : Option Claim} {n : ℕ}
    (hkind : kindOf c = Kind.int ∨ kindOf c = Kind.unk)
    (hcap : (kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ k : Claim, c = some k →
      ints.length ≤ claimCap k) :
    ∃ s1 o1, (s1 = St.NZERO ∨ s1 = St.NINT) ∧ o1 ≤ ofsMax - 1 ∧
      runL (nRegs s0 c 0 n) (ints.map (· + digit0)) = some (nRegs s1 c o1 n) ∧
      Contrib c 0 ints 0 0 (traceL (nRegs s0 c 0 n) (ints.map (· + digit0))) := by
  have hnstr : inStr s0 = false := by rcases hs0 with rfl | rfl <;> decide
  have hval0 : (if Step.inValP s0 = true then (0 : ℕ) else 0) = 0 := by split <;> rfl
  have hdst : s0 = St.PVAL ∨ s0 = St.NSIGN ∨ s0 = St.NINT := by
    rcases hs0 with h | h <;> tauto
  rcases hwf with rfl | ⟨d, ds, rfl, hd1, hd9, hds⟩
  · refine ⟨St.NZERO, 1, Or.inl rfl, by simp only [ofsMax]; omega, ?_⟩
    have hstep : stepSt (kindOf c) true s0 digit0 = some St.NZERO := by
      rcases hs0 with rfl | rfl
      · exact stepSt_pval_digit0 hkind true
      · exact stepSt_nsign_digit0 _ _
    obtain ⟨sa, ka⟩ := nstepE (s := s0) (s' := St.NZERO) (c := c) (o := 0) (o' := 1) (n := n)
      hnstr (by decide) hstep (dEmit_of_digit (by decide) hdst)
      (fun hk k hck => by have := hcap hk k hck; simp at this; omega)
      (by rw [hval0]; simp)
    have := runC1 ⟨sa, ka⟩
    simp only [List.map_cons, List.map_nil, Nat.zero_add] at this ⊢
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    rw [show digit0 - digit0 = 0 from Nat.sub_self _] at h2
    exact h2
  · have hdig : Model.isDigitNz (d + digit0) = true := isDigitNz_add hd1 hd9
    have hstep : stepSt (kindOf c) true s0 (d + digit0) = some St.NINT := by
      rcases hs0 with rfl | rfl
      · exact stepSt_pval_dnz hkind true hdig
      · exact stepSt_nsign_dnz _ _ hdig
    obtain ⟨sa, ka⟩ := nstepE (s := s0) (s' := St.NINT) (c := c) (o := 0) (o' := 1) (n := n)
      hnstr (by decide) hstep (dEmit_of_digit (isDigit_add hd9) hdst)
      (fun hk k hck => by have := hcap hk k hck; simp at this; omega)
      (by rw [hval0]; simp)
    obtain ⟨sb, kb⟩ := nint_digits_run ds hds c 1 n (by simp only [ofsMax]; omega)
      (fun hk k hck => by
        have h1 := hcap hk k hck
        simp only [List.length_cons] at h1
        omega)
    refine ⟨St.NINT, min (1 + ds.length) (ofsMax - 1), Or.inr rfl, by omega, ?_⟩
    have hj := runCC (runC1 ⟨sa, ka⟩).1 (runC1 ⟨sa, ka⟩).2 sb kb
    rw [show d + digit0 - digit0 = d from add_sub_digit0 d] at hj
    simp only [List.map_cons, Nat.zero_add] at hj ⊢
    refine ⟨?_, ?_⟩
    · have := hj.1
      simpa using this
    · have := hj.2
      simpa using this

/-! ## Whole values -/

set_option maxHeartbeats 1000000 in
theorem num_run {nm : SNum} (hwf : nm.WF) {c : Option Claim} {n : ℕ}
    (hkind : kindOf c = Kind.unk ∨ (kindOf c = Kind.int ∧ nm.frac = [] ∧ nm.exp = none))
    (hcap : (kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ k : Claim, c = some k →
      nm.ints.length ≤ claimCap k) :
    ∃ r', runL (nRegs St.PVAL c 0 n) nm.bytes = some r' ∧ AtE c n r' ∧
      Contrib c 0 nm.ints (if nm.neg then 1 else 0) 0
        (traceL (nRegs St.PVAL c 0 n) nm.bytes) := by
  have hkindIU : kindOf c = Kind.int ∨ kindOf c = Kind.unk := by
    rcases hkind with h | ⟨h, _, _⟩ <;> tauto
  -- the optional sign
  obtain ⟨s0, hs0, hsgn, ksgn⟩ : ∃ s0, (s0 = St.PVAL ∨ s0 = St.NSIGN) ∧
      runL (nRegs St.PVAL c 0 n) (if nm.neg then [minus] else [])
        = some (nRegs s0 c 0 n) ∧
      Contrib c 0 [] (if nm.neg then 1 else 0) 0
        (traceL (nRegs St.PVAL c 0 n) (if nm.neg then [minus] else [])) := by
    by_cases hneg : nm.neg
    · refine ⟨St.NSIGN, Or.inr rfl, ?_, ?_⟩
      · rw [if_pos hneg]
        exact (runC1 (nstepM (stepSt_pval_minus hkindIU true))).1
      · rw [if_pos hneg, if_pos hneg]
        exact (nstepM (stepSt_pval_minus hkindIU true)).2
    · refine ⟨St.PVAL, Or.inl rfl, by rw [if_neg hneg]; rfl, ?_⟩
      rw [if_neg hneg, if_neg hneg]
      exact contrib_of_quiet quiet_nil c
  -- the integer part
  obtain ⟨s1, o1, hs1, ho1, hints, kints⟩ := ints_run (n := n) hs0 hwf.1 hkindIU hcap
  -- the fractional part
  obtain ⟨s2, hs2, hfrac, qfrac⟩ : ∃ s2, (s2 = St.NZERO ∨ s2 = St.NINT ∨ s2 = St.NFRAC) ∧
      runL (nRegs s1 c o1 n) (fracB nm) = some (nRegs s2 c o1 n) ∧
      Quiet (traceL (nRegs s1 c o1 n) (fracB nm)) := by
    by_cases hf : nm.frac = []
    · exact ⟨s1, by tauto, by rw [fracB, if_pos hf]; rfl,
        by rw [fracB, if_pos hf]; exact quiet_nil⟩
    · have hunk : kindOf c = Kind.unk := by
        rcases hkind with h | ⟨_, h2, _⟩
        · exact h
        · exact absurd h2 hf
      refine ⟨St.NFRAC, by tauto, ?_, ?_⟩
      · rw [fracB, if_neg hf]; exact (frac_run hs1 hf hwf.2.1 ho1 hunk).1
      · rw [fracB, if_neg hf]; exact (frac_run hs1 hf hwf.2.1 ho1 hunk).2
  -- the exponent
  obtain ⟨s3, hs3, hexp, qexp⟩ : ∃ s3, endValState s3 = true ∧
      runL (nRegs s2 c o1 n) (expB nm) = some (nRegs s3 c o1 n) ∧
      Quiet (traceL (nRegs s2 c o1 n) (expB nm)) := by
    cases hx : nm.exp with
    | none =>
      refine ⟨s2, ?_, by rw [expB, hx]; rfl, by rw [expB, hx]; exact quiet_nil⟩
      rcases hs2 with rfl | rfl | rfl <;> decide
    | some e =>
      have hunk : kindOf c = Kind.unk := by
        rcases hkind with h | ⟨_, _, h3⟩
        · exact h
        · rw [hx] at h3; exact absurd h3 (by simp)
      have hew : (e.letter = lowerE ∨ e.letter = upperE) ∧
          (match e.sign with | none => True | some sg => sg = plus ∨ sg = minus) ∧
          e.digits ≠ [] ∧ ∀ x ∈ e.digits, x ≤ 9 := by
        have := hwf.2.2
        rw [hx] at this
        exact this
      refine ⟨St.NEXP, by decide, ?_, ?_⟩
      · rw [expB, hx]
        exact (exp_run hs2 hew.1 hew.2.1 hew.2.2.1 hew.2.2.2 ho1 (fun _ => hunk)).1
      · rw [expB, hx]
        exact (exp_run hs2 hew.1 hew.2.1 hew.2.2.1 hew.2.2.2 ho1 (fun _ => hunk)).2
  refine ⟨nRegs s3 c o1 n, ?_, ⟨hs3, rfl, rfl, rfl⟩, ?_⟩ <;>
    [skip; skip] <;>
    · rw [SNum_bytes_eq]
      have j1 := runCC hsgn ksgn hints kints
      have j2 := runCC hfrac (contrib_of_quiet qfrac c) hexp (contrib_of_quiet qexp c)
      have j3 := runCC j1.1 j1.2 j2.1 j2.2
      simp only [Nat.zero_add, Nat.add_zero, List.nil_append, List.append_nil,
        List.append_assoc] at j3
      first
        | exact j3.1
        | exact j3.2

theorem true_run {c : Option Claim} {n : ℕ}
    (hkind : kindOf c = Kind.bool ∨ kindOf c = Kind.unk) :
    runL (nRegs St.PVAL c 0 n) trueLit = some (nRegs St.AVAL c 0 n) ∧
      Contrib c 0 [] 0 1 (traceL (nRegs St.PVAL c 0 n) trueLit) := by
  have h1 := runQ1 (nstepQ (s := St.PVAL) (s' := St.T1) (c := c) (o := 0) (o' := 0) (n := n)
    (by decide) (by decide) (stepSt_pval_t hkind true) (by decide) (by decide) (by decide)
    (by simp))
  have h2 := runQ1 (nstepV (s := St.T1) (s' := St.T2) (b := lowerR) (c := c) (o := 0) (n := n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) rfl)
  have h3 := runQ1 (nstepV (s := St.T2) (s' := St.T3) (b := lowerU) (c := c) (o := 0) (n := n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) rfl)
  have h4 := runC1 (nstepT (c := c) (o := 0) (n := n) (by simp))
  have j3 := runCC h3.1 (contrib_of_quiet h3.2 c) h4.1 h4.2
  have j2 := runCC h2.1 (contrib_of_quiet h2.2 c) j3.1 j3.2
  have j1 := runCC h1.1 (contrib_of_quiet h1.2 c) j2.1 j2.2
  simpa using j1

theorem false_run {c : Option Claim} {n : ℕ}
    (hkind : kindOf c = Kind.bool ∨ kindOf c = Kind.unk) :
    runL (nRegs St.PVAL c 0 n) falseLit = some (nRegs St.AVAL c 0 n) ∧
      Quiet (traceL (nRegs St.PVAL c 0 n) falseLit) := by
  have h1 := runQ1 (nstepQ (s := St.PVAL) (s' := St.F1) (c := c) (o := 0) (o' := 0) (n := n)
    (by decide) (by decide) (stepSt_pval_f hkind true) (by decide) (by decide) (by decide)
    (by simp))
  have h2 := runQ1 (nstepV (s := St.F1) (s' := St.F2) (b := lowerA) (c := c) (o := 0) (n := n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) rfl)
  have h3 := runQ1 (nstepV (s := St.F2) (s' := St.F3) (b := 0x6C) (c := c) (o := 0) (n := n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) rfl)
  have h4 := runQ1 (nstepV (s := St.F3) (s' := St.F4) (b := 0x73) (c := c) (o := 0) (n := n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) rfl)
  have h5 := runQ1 (nstepV (s := St.F4) (s' := St.AVAL) (b := lowerE) (c := c) (o := 0) (n := n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) rfl)
  have j4 := runQQ h4.1 h4.2 h5.1 h5.2
  have j3 := runQQ h3.1 h3.2 j4.1 j4.2
  have j2 := runQQ h2.1 h2.2 j3.1 j3.2
  have j1 := runQQ h1.1 h1.2 j2.1 j2.2
  simpa using j1

theorem null_run {c : Option Claim} {n : ℕ} (hkind : kindOf c = Kind.unk) :
    runL (nRegs St.PVAL c 0 n) nullLit = some (nRegs St.AVAL c 0 n) ∧
      Quiet (traceL (nRegs St.PVAL c 0 n) nullLit) := by
  have h1 := runQ1 (nstepQ (s := St.PVAL) (s' := St.N1) (c := c) (o := 0) (o' := 0) (n := n)
    (by decide) (by decide) (stepSt_pval_n hkind true) (by decide) (by decide) (by decide)
    (by simp))
  have h2 := runQ1 (nstepV (s := St.N1) (s' := St.N2) (b := lowerU) (c := c) (o := 0) (n := n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) rfl)
  have h3 := runQ1 (nstepV (s := St.N2) (s' := St.N3) (b := 0x6C) (c := c) (o := 0) (n := n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) rfl)
  have h4 := runQ1 (nstepV (s := St.N3) (s' := St.AVAL) (b := 0x6C) (c := c) (o := 0) (n := n)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) rfl)
  have j3 := runQQ h3.1 h3.2 h4.1 h4.2
  have j2 := runQQ h2.1 h2.2 j3.1 j3.2
  have j1 := runQQ h1.1 h1.2 j2.1 j2.2
  simpa using j1

theorem str_value_run {body : List SE} (hwf : ∀ e ∈ body, e.WF) {c : Option Claim} {n : ℕ}
    (hkind : kindOf c = Kind.str ∨ kindOf c = Kind.unk)
    (hcap : (kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ k : Claim, c = some k →
      body.length ≤ claimCap k)
    (hascii : (kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ e ∈ body, e.mcp < 0x80) :
    ∃ r', runL (nRegs St.PVAL c 0 n) (SV.bytes (.str body)) = some r' ∧ AtE c n r' ∧
      Contrib c 0 (mcps body) 0 0
        (traceL (nRegs St.PVAL c 0 n) (SV.bytes (.str body))) := by
  have h1 := runQ1 (nstepQ (s := St.PVAL) (s' := St.STR) (b := quote) (c := c) (o := 0)
    (o' := 0) (n := n) (by decide) (by decide) (stepSt_pval_quote hkind) (by decide)
    (by decide) (by decide) (by simp))
  have hstart : nRegs St.STR c 0 n = sRegs Sub.PLAIN 0 c 0 n := rfl
  rw [hstart] at h1
  obtain ⟨h2, k2⟩ := str_body_run body hwf c 0 n (by simp only [ofsMax]; omega)
    (by simpa using hcap) hascii
  have ho' : min (0 + body.length) (ofsMax - 1) ≤ ofsMax - 1 := by omega
  obtain ⟨h3, q3⟩ := step_closeStr (c := c) (o := min (0 + body.length) (ofsMax - 1)) (n := n) ho'
  have j2 := runCC h2 k2 (runQ1 ⟨h3, q3⟩).1 (contrib_of_quiet (runQ1 ⟨h3, q3⟩).2 c)
  have j1 := runCC h1.1 (contrib_of_quiet h1.2 c) j2.1 j2.2
  refine ⟨nRegs St.AVAL c (min (0 + body.length) (ofsMax - 1)) n, ?_,
    ⟨endValState_aval, rfl, rfl, rfl⟩, ?_⟩ <;>
    · simp only [SV.bytes]
      rw [show quote :: (seBytes body ++ [quote]) = [quote] ++ (seBytes body ++ [quote]) from rfl]
      first
        | exact j1.1
        | (have := j1.2; simpa using this)

/-! ## Kinds -/

theorem kindOf_none' : kindOf none = Kind.unk := rfl

theorem kindOf_str {k : Claim} (h : isStrClaim k = true) : kindOf (some k) = Kind.str := by
  simp [kindOf, h]

theorem kindOf_int {k : Claim} (h1 : isStrClaim k = false) (h2 : isIntClaim k = true) :
    kindOf (some k) = Kind.int := by simp [kindOf, h1, h2]

theorem kindOf_bool {k : Claim} (h1 : isStrClaim k = false) (h2 : isIntClaim k = false) :
    kindOf (some k) = Kind.bool := by simp [kindOf, h1, h2]

/-! ## Any value -/

theorem value_run {v : SV} (hwf : v.WF) {c : Option Claim} {n : ℕ} (hok : SV.Ok c v) :
    ∃ r', runL (nRegs St.PVAL c 0 n) v.bytes = some r' ∧ AtE c n r' ∧
      Contrib c 0 v.vals v.sign v.trues (traceL (nRegs St.PVAL c 0 n) v.bytes) := by
  by_cases hc : c = none
  · have hk : kindOf c = Kind.unk := by rw [hc]; rfl
    have hvac : ∀ k : Claim, ¬ c = some k := by intro k h; rw [hc] at h; simp at h
    cases v with
    | str body =>
      exact str_value_run hwf (Or.inr hk) (fun _ k hck => absurd hck (hvac k))
        (fun hkk => absurd hkk (by rw [hk]; simp))
    | num nm => exact num_run hwf (Or.inl hk) (fun _ k hck => absurd hck (hvac k))
    | btrue =>
      obtain ⟨a, b⟩ := true_run (c := c) (n := n) (Or.inr hk)
      exact ⟨nRegs St.AVAL c 0 n, a, ⟨endValState_aval, rfl, rfl, rfl⟩, b⟩
    | bfalse =>
      obtain ⟨a, b⟩ := false_run (c := c) (n := n) (Or.inr hk)
      exact ⟨nRegs St.AVAL c 0 n, a, ⟨endValState_aval, rfl, rfl, rfl⟩, contrib_of_quiet b c⟩
    | null =>
      obtain ⟨a, b⟩ := null_run (c := c) (n := n) hk
      exact ⟨nRegs St.AVAL c 0 n, a, ⟨endValState_aval, rfl, rfl, rfl⟩, contrib_of_quiet b c⟩
  · obtain ⟨k, hk⟩ : ∃ k, c = some k := by
      cases hcc : c with
      | none => exact absurd hcc hc
      | some k => exact ⟨k, rfl⟩
    have hok2 : (if isStrClaim k = true then
          ∃ body, v = .str body ∧ (∀ e ∈ body, e.mcp < 0x80) ∧ body.length ≤ claimCap k
        else if isIntClaim k = true then
          ∃ nm, v = .num nm ∧ nm.frac = [] ∧ nm.exp = none ∧ nm.ints.length ≤ claimCap k
        else v = .btrue ∨ v = .bfalse) := by
      have : SV.Ok (some k) v := by rw [← hk]; exact hok
      exact this
    by_cases hs : isStrClaim k = true
    · rw [if_pos hs] at hok2
      obtain ⟨body, rfl, hascii, hlen⟩ := hok2
      have hkd : kindOf c = Kind.str := by rw [hk]; exact kindOf_str hs
      exact str_value_run hwf (Or.inl hkd)
        (fun _ k' hck => by
          rw [hk, Option.some.injEq] at hck; subst hck; exact hlen)
        (fun _ => hascii)
    · rw [if_neg hs] at hok2
      simp only [Bool.not_eq_true] at hs
      by_cases hi : isIntClaim k = true
      · rw [if_pos hi] at hok2
        obtain ⟨nm, rfl, hfr, hex, hlen⟩ := hok2
        have hkd : kindOf c = Kind.int := by rw [hk]; exact kindOf_int hs hi
        exact num_run hwf (Or.inr ⟨hkd, hfr, hex⟩)
          (fun _ k' hck => by rw [hk, Option.some.injEq] at hck; subst hck; exact hlen)
      · rw [if_neg hi] at hok2
        simp only [Bool.not_eq_true] at hi
        have hkd : kindOf c = Kind.bool := by rw [hk]; exact kindOf_bool hs hi
        rcases hok2 with rfl | rfl
        · obtain ⟨a, b⟩ := true_run (c := c) (n := n) (Or.inl hkd)
          exact ⟨nRegs St.AVAL c 0 n, a, ⟨endValState_aval, rfl, rfl, rfl⟩, b⟩
        · obtain ⟨a, b⟩ := false_run (c := c) (n := n) (Or.inl hkd)
          exact ⟨nRegs St.AVAL c 0 n, a, ⟨endValState_aval, rfl, rfl, rfl⟩, contrib_of_quiet b c⟩

/-! ## The claim a key names -/

theorem claimName_inj : ∀ a b : Claim, claimName a = claimName b → a = b := by decide

theorem find_claim_some {cps : List ℕ} {k : Claim} (h : cps = claimName k) :
    (List.finRange nClaims).find? (fun k' : Claim => decide (cps = claimName k')) = some k := by
  cases hf : (List.finRange nClaims).find? (fun k' : Claim => decide (cps = claimName k')) with
  | none => exact absurd (List.find?_eq_none.mp hf k (List.mem_finRange k)) (by simp [h])
  | some k' =>
    have hk' := List.find?_some hf
    simp only [decide_eq_true_eq] at hk'
    rw [claimName_inj k k' (by rw [← h, ← hk'])]

theorem find_claim_none {cps : List ℕ}
    (h : (List.finRange nClaims).find? (fun k' : Claim => decide (cps = claimName k')) = none)
    (k : Claim) : cps ≠ claimName k := by
  intro he
  exact absurd (List.find?_eq_none.mp h k (List.mem_finRange k)) (by simp [he])

/-- The key-close position's match flag is the claim test. -/
theorem match_flag (cps : List ℕ) (k : Claim) :
    (mAfter k true 0 cps && decide (kIdxAfter 0 cps.length = (claimName k).length))
      = decide (cps = claimName k) := by
  by_cases h : cps = claimName k
  · have := (match_iff k cps).mpr h
    rw [Bool.and_eq_true, decide_eq_true_eq] at this
    subst h
    simp only [decide_true, Bool.and_eq_true, decide_eq_true_eq]
    exact this
  · simp only [h, decide_false]
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    exact h ((match_iff k cps).mp hcon)

/-! ## The opening quote of a member -/

theorem step_openQuote {s : St} (hs : s = St.OBJ ∨ s = St.SEP) {c0 : Option Claim} {n : ℕ}
    {r : Regs} (hr : AtS s c0 n r) :
    step r quote = some (kRegs Sub.PLAIN 0 0 (Vector.ofFn fun _ => true) (n + 1)) ∧
      Silent (r, quote) := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have hnstr : inStr s = false := by rcases hs with rfl | rfl <;> decide
  have hnk : s ≠ St.KEY := by rcases hs with rfl | rfl <;> decide
  have hnval : Step.inValP s = false := by rcases hs with rfl | rfl <;> decide
  have e1 : stepSub (inStr r.st) r.sub quote = some Sub.PLAIN := by
    rw [h1, hnstr]; exact stepSub_notInStr _ _
  have e2 : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st quote = some St.KEY := by
    rw [h1, h2]
    simp only [decide_true]
    rcases hs with rfl | rfl
    · exact stepSt_obj_quote _ _
    · exact stepSt_sep_quote _ _
  have hve : (signals r quote St.KEY).vEmit = false :=
    sig_vEmit_of (by rw [h1]; exact hnstr) (Or.inl (by decide))
  have hw := sig_write_of_vEmit hve
  have hks : (signals r quote St.KEY).keyStart = true := by
    rw [sig_keyStart, h1]; simp [hnk]
  have hkc : (signals r quote St.KEY).keyClose = false := by
    rw [Step.sig_keyClose, Step.keyCloseB, h1]; simp [hnk]
  constructor
  · rw [step_eq e1 e2 (by rw [hw]; simp) (by rw [hw]; simp)]
    congr 1
    simp only [mkNext, kRegs, Regs.mk.injEq, hks, hkc, hve, h1, h2, h4, hnk, hnval,
      Bool.false_eq_true, if_false, if_true]
    and_intros <;>
      first
        | trivial
        | (exact Vector.ext fun t ht => by simp)
        | simp [Sub.PLAIN, Sub.H1, Sub.H2, Sub.H3]
  · refine silent_sig (by rw [h1]; exact hnk) ?_ ?_ ?_
    · rw [← RunList.sig_vEmit_indep r quote St.KEY r.st]; exact hve
    · rw [Step.sig_minusFlag]; simp
    · rw [Step.sig_trueDone]; simp

theorem claim_iff {m : SMem} (k : Claim) : m.claim = some k ↔ m.mkey = claimName k := by
  constructor
  · intro h
    have := List.find?_some (p := fun k' : Claim => decide (m.mkey = claimName k')) h
    simpa using this
  · exact find_claim_some

set_option maxHeartbeats 1000000 in
theorem member_run {m : SMem} (hm : m.WF) {s : St} (hs : s = St.OBJ ∨ s = St.SEP)
    {c0 : Option Claim} {n : ℕ} {r : Regs} (hr : AtS s c0 n r) :
    ∃ r', runL r m.bytes = some r' ∧ AtE m.claim (n + 1) r' ∧
      Contrib m.claim 1 m.val.vals m.val.sign m.val.trues (traceL r m.bytes) := by
  obtain ⟨hws0, hws1, hws2, hws3, hkey, hvwf, hvok⟩ := hm
  have hwsS : wsState s = true := by rcases hs with rfl | rfl <;> decide
  set mv : Vector Bool nClaims :=
    Vector.ofFn (fun k : Claim => mAfter k ((Vector.ofFn fun _ : Claim => true)[k]) 0 (mcps m.key))
    with hmv
  set i0 : ℕ := kIdxAfter 0 m.key.length with hi0
  have hmvk : ∀ k : Claim, (mv[k] && decide (i0 = (claimName k).length))
      = decide (m.mkey = claimName k) := by
    intro k
    simp only [hmv, hi0, Vector.getElem_ofFn, Fin.getElem_fin, SMem.mkey]
    have hml : m.key.length = (mcps m.key).length := (mcps_length m.key).symm
    simp only [hml]
    exact match_flag (mcps m.key) k
  have hfind : ((List.finRange nClaims).find? fun k : Claim =>
      (mv[k] && decide (i0 = (claimName k).length))) = m.claim := by
    rw [SMem.claim]
    congr 1
    funext k
    exact hmvk k
  -- the value part
  obtain ⟨rv, ev, av, kv⟩ := value_run (v := m.val) hvwf (c := m.claim) (n := n + 1) hvok
  obtain ⟨r9, e9, a9, q9⟩ := ws_run_AtE av hws3
  have j8 := runCC ev kv e9 (contrib_of_quiet q9 m.claim)
  -- ws2 at PVAL
  obtain ⟨e7, q7⟩ := ws_run_normal (s := St.PVAL) (c := m.claim) (n := n + 1) (by decide) hws2
  have j7 := runCC e7 (contrib_of_quiet q7 m.claim) j8.1 j8.2
  -- the key close and the colon
  obtain ⟨r4, e4, a4, hpm4, hpe4, hpmi4, hpt4⟩ :=
    step_closeKey (i := i0) (n := n + 1) (mv := mv)
  rw [hfind] at a4
  obtain ⟨r5, hws1run, hws1a, hws1q⟩ := ws_run_AtS a4 (by decide) hws1
  have e6 : step r5 colon = some (normal St.PVAL m.claim (n + 1)) :=
    step_struct hws1a (by decide) (by decide) (by decide) (by decide) (by decide)
      (stepSt_akey_colon _ _)
  have q6 : Silent (r5, colon) :=
    silent_of (by rw [hws1a.1]; decide)
      (sig_vEmit_of (by rw [hws1a.1]; decide) (Or.inl (by decide)))
      (by rw [hws1a.1]; decide) (by rw [hws1a.1]; decide)
  have j6 := runCC (runQ1 ⟨e6, q6⟩).1 (contrib_of_quiet (runQ1 ⟨e6, q6⟩).2 m.claim) j7.1 j7.2
  have j5 := runCC hws1run (contrib_of_quiet hws1q m.claim) j6.1 j6.2
  have j4 : runL (kRegs Sub.PLAIN 0 i0 mv (n + 1))
        ([quote] ++ (m.ws1 ++ ([colon] ++ (m.ws2 ++ (m.val.bytes ++ m.ws3))))) = some r9 ∧
      Contrib m.claim 1 m.val.vals m.val.sign m.val.trues
        (traceL (kRegs Sub.PLAIN 0 i0 mv (n + 1))
          ([quote] ++ (m.ws1 ++ ([colon] ++ (m.ws2 ++ (m.val.bytes ++ m.ws3)))))) := by
    have hc4 : Contrib m.claim 1 [] 0 0 (traceL (kRegs Sub.PLAIN 0 i0 mv (n + 1)) [quote]) := by
      rw [RunList.traceL_single]
      refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
      · rw [cMatch_cons, hpm4 k, hmvk k]
        by_cases hk : m.claim = some k
        · have hx : m.mkey = claimName k := (claim_iff k).mp hk
          simp [hk, hx]
        · have hx : ¬ (m.mkey = claimName k) := fun hy => hk ((claim_iff k).mpr hy)
          simp [hk, hx]
      · rw [valsT_cons, hpe4 k]; simp
      · rw [cSign_cons, hpmi4 k]; simp
      · rw [cTrue_cons, hpt4 k]; simp
    have := runCC (runC1 ⟨e4, hc4⟩).1 hc4 j5.1 j5.2
    simpa using this
  -- the key body
  obtain ⟨e3, q3⟩ := key_body_run m.key hkey 0 (n + 1) (by simp only [kIdxMax]; omega)
    (Vector.ofFn fun _ : Claim => true)
  rw [show kIdxAfter 0 m.key.length = i0 from rfl] at e3
  have j3 := runCC e3 (contrib_of_quiet q3 m.claim) j4.1 j4.2
  -- the opening quote
  obtain ⟨r0, hws0run, hws0a, hws0q⟩ := ws_run_AtS hr hwsS hws0
  obtain ⟨e2, q2⟩ := step_openQuote hs hws0a
  have j2 := runCC (runQ1 ⟨e2, q2⟩).1 (contrib_of_quiet (runQ1 ⟨e2, q2⟩).2 m.claim) j3.1 j3.2
  have j1 := runCC hws0run (contrib_of_quiet hws0q m.claim) j2.1 j2.2
  refine ⟨r9, ?_, a9, ?_⟩ <;>
    · have hb : m.bytes = m.ws0 ++ ([quote] ++ (seBytes m.key ++ ([quote] ++ (m.ws1 ++
          ([colon] ++ (m.ws2 ++ (m.val.bytes ++ m.ws3))))))) := by
        simp [SMem.bytes, List.append_assoc]
      rw [hb]
      simp only [Nat.zero_add, Nat.add_zero, List.nil_append, List.append_nil] at j1
      first
        | exact j1.1
        | exact j1.2

/-! ## The whole member list -/

def BContrib (ms : List SMem) (T : List (Regs × ℕ)) : Prop :=
  (∀ k : Claim, cMatch k T = bMatch ms k) ∧ (∀ k : Claim, valsT k T = bVals ms k) ∧
    (∀ k : Claim, cSign k T = bSign ms k) ∧ (∀ k : Claim, cTrue k T = bTrue ms k)

theorem bcontrib_quiet {T : List (Regs × ℕ)} (h : Quiet T) : BContrib [] T :=
  ⟨fun k => by rw [cMatch_of_quiet h]; rfl, fun k => by rw [valsT_of_quiet h]; rfl,
   fun k => by rw [cSign_of_quiet h]; rfl, fun k => by rw [cTrue_of_quiet h]; rfl⟩

theorem bcontrib_append {ms1 ms2 : List SMem} {T1 T2 : List (Regs × ℕ)}
    (h1 : BContrib ms1 T1) (h2 : BContrib ms2 T2) : BContrib (ms1 ++ ms2) (T1 ++ T2) := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [cMatch_append, h1.1 k, h2.1 k, bMatch, bMatch, bMatch]; simp
  · rw [valsT_append, h1.2.1 k, h2.2.1 k, bVals, bVals, bVals]; simp
  · rw [cSign_append, h1.2.2.1 k, h2.2.2.1 k, bSign, bSign, bSign]; simp
  · rw [cTrue_append, h1.2.2.2 k, h2.2.2.2 k, bTrue, bTrue, bTrue]; simp

theorem bcontrib_single {m : SMem} {T : List (Regs × ℕ)}
    (h : Contrib m.claim 1 m.val.vals m.val.sign m.val.trues T) : BContrib [m] T := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [h.1 k, bMatch]; simp
  · rw [h.2.1 k, bVals]; simp
  · rw [h.2.2.1 k, bSign]; simp
  · rw [h.2.2.2 k, bTrue]; simp

theorem runBB {r r1 rf : Regs} {L1 L2 : List ℕ} {ms1 ms2 : List SMem}
    (h1 : runL r L1 = some r1) (k1 : BContrib ms1 (traceL r L1))
    (h2 : runL r1 L2 = some rf) (k2 : BContrib ms2 (traceL r1 L2)) :
    runL r (L1 ++ L2) = some rf ∧ BContrib (ms1 ++ ms2) (traceL r (L1 ++ L2)) := by
  refine ⟨by rw [RunList.runL_append_of h1]; exact h2, ?_⟩
  rw [RunList.traceL_append h1]
  exact bcontrib_append k1 k2

theorem members_run : ∀ (ms : List SMem), (∀ m ∈ ms, m.WF) →
    ∀ {c0 : Option Claim} {n : ℕ} {r : Regs}, AtE c0 n r →
    ∃ r' c, runL r ((ms.map fun m' => comma :: m'.bytes).flatten) = some r' ∧
      AtE c (n + ms.length) r' ∧
      BContrib ms (traceL r ((ms.map fun m' => comma :: m'.bytes).flatten)) := by
  intro ms
  induction ms with
  | nil =>
    intro _ c0 n r hr
    exact ⟨r, c0, rfl, by simpa using hr, bcontrib_quiet quiet_nil⟩
  | cons m ms ih =>
    intro hms c0 n r hr
    obtain ⟨r1, e1, a1, q1⟩ := step_endVal_comma hr
    obtain ⟨r2, e2, a2, k2⟩ := member_run (hms m (List.mem_cons_self ..)) (Or.inr rfl) a1
    obtain ⟨r3, c3, e3, a3, k3⟩ := ih (fun x hx => hms x (List.mem_cons_of_mem _ hx)) a2
    refine ⟨r3, c3, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, List.cons_append]
      rw [show comma :: (m.bytes ++ (ms.map fun m' => comma :: m'.bytes).flatten)
          = [comma] ++ (m.bytes ++ (ms.map fun m' => comma :: m'.bytes).flatten) from rfl,
        RunList.runL_append_of (by rw [RunList.runL_single]; exact e1),
        RunList.runL_append_of e2]
      exact e3
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ms.length] using a3
    · simp only [List.map_cons, List.flatten_cons, List.cons_append]
      rw [show comma :: (m.bytes ++ (ms.map fun m' => comma :: m'.bytes).flatten)
          = [comma] ++ (m.bytes ++ (ms.map fun m' => comma :: m'.bytes).flatten) from rfl,
        RunList.traceL_append (by rw [RunList.runL_single]; exact e1),
        RunList.traceL_append e2]
      have hq : BContrib [] (traceL r [comma]) := by
        rw [RunList.traceL_single]; exact bcontrib_quiet (quiet_single q1)
      have := bcontrib_append hq (bcontrib_append (bcontrib_single k2) k3)
      simpa using this

theorem body_close_run {ms : List SMem} (hms : ∀ m ∈ ms, m.WF) {we : List ℕ} (hwe : IsWs we)
    {c0 : Option Claim} {n : ℕ} {r : Regs} (hr : AtS St.OBJ c0 n r) :
    ∃ r' c, runL r (bodyBytes ms we ++ [rbrace]) = some r' ∧
      AtS St.END c (n + ms.length) r' ∧
      BContrib ms (traceL r (bodyBytes ms we ++ [rbrace])) := by
  cases ms with
  | nil =>
    obtain ⟨r1, e1, a1, q1⟩ := ws_run_AtS hr (by decide) hwe
    have e2 : step r1 rbrace = some (normal St.END c0 n) :=
      step_struct a1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (stepSt_obj_rbrace _ _)
    have q2 : Silent (r1, rbrace) :=
      silent_of (by rw [a1.1]; decide)
        (sig_vEmit_of (by rw [a1.1]; decide) (Or.inl (by decide)))
        (by rw [a1.1]; decide) (by rw [a1.1]; decide)
    refine ⟨normal St.END c0 n, c0, ?_, ?_, ?_⟩
    · rw [show bodyBytes [] we = we from rfl, RunList.runL_append_of e1, RunList.runL_single]
      exact e2
    · exact ⟨rfl, rfl, rfl, by simp only [List.length_nil, Nat.add_zero]; rfl⟩
    · rw [show bodyBytes [] we = we from rfl, RunList.traceL_append e1]
      exact bcontrib_quiet (quiet_append q1 (by rw [RunList.traceL_single]; exact quiet_single q2))
  | cons m ms =>
    obtain ⟨r1, e1, a1, k1⟩ := member_run (hms m (List.mem_cons_self ..)) (Or.inl rfl) hr
    obtain ⟨r2, c2, e2, a2, k2⟩ := members_run ms (fun x hx => hms x (List.mem_cons_of_mem _ hx)) a1
    obtain ⟨r3, e3, a3, q3⟩ := step_endVal_rbrace a2
    refine ⟨r3, c2, ?_, ?_, ?_⟩
    · rw [show bodyBytes (m :: ms) we
          = m.bytes ++ (ms.map fun m' => comma :: m'.bytes).flatten from rfl,
        List.append_assoc, RunList.runL_append_of e1, RunList.runL_append_of e2,
        RunList.runL_single]
      exact e3
    · refine ⟨a3.1, a3.2.1, a3.2.2.1, ?_⟩
      rw [a3.2.2.2]
      simp only [List.length_cons]
      omega
    · rw [show bodyBytes (m :: ms) we
          = m.bytes ++ (ms.map fun m' => comma :: m'.bytes).flatten from rfl,
        List.append_assoc, RunList.traceL_append e1, RunList.traceL_append e2]
      have hq : BContrib [] (traceL r2 [rbrace]) := by
        rw [RunList.traceL_single]; exact bcontrib_quiet (quiet_single q3)
      have := bcontrib_append (bcontrib_single k1) (bcontrib_append k2 hq)
      simpa using this

/-- **The forward run.** A well-formed serialization drives the automaton to
`END`, starting `body.length` members, and its read-outs are the members'
slots. -/
theorem ser_run {sr : Ser} (hwf : sr.SWF) :
    ∃ r', runL Regs.init sr.bytes = some r' ∧ r'.st = St.END ∧ r'.sub = Sub.PLAIN ∧
      r'.nMem = sr.body.length ∧ BContrib sr.body (traceL Regs.init sr.bytes) := by
  obtain ⟨hpre, hwe, hpost, hms⟩ := hwf
  rw [init_eq_normal]
  obtain ⟨e1, q1⟩ := ws_run_normal (s := St.PRE) (c := (none : Option Claim)) (n := 0)
    (by decide) hpre
  have e2 : step (normal St.PRE none 0) lbrace = some (normal St.OBJ none 0) :=
    step_struct (atS_normal _ _ _) (by decide) (by decide) (by decide) (by decide) (by decide)
      (stepSt_pre_lbrace _ _)
  have q2 : Silent (normal St.PRE none 0, lbrace) :=
    silent_of (by decide) (sig_vEmit_of (by decide) (Or.inl (by decide))) (by decide) (by decide)
  obtain ⟨r3, c3, e3, a3, k3⟩ := body_close_run hms hwe (atS_normal St.OBJ none 0)
  obtain ⟨r4, e4, a4, q4⟩ := ws_run_AtS a3 (by decide) hpost
  have hb : sr.bytes = sr.pre ++ ([lbrace] ++
      ((bodyBytes sr.body sr.wsEmpty ++ [rbrace]) ++ sr.post)) := by
    rw [Ser.bytes]; simp only [List.append_assoc]
  refine ⟨r4, ?_, a4.1, a4.2.1, ?_, ?_⟩
  · rw [hb, RunList.runL_append_of e1,
      RunList.runL_append_of (by rw [RunList.runL_single]; exact e2),
      RunList.runL_append_of e3]
    exact e4
  · rw [a4.2.2.2]
    simp
  · rw [hb, RunList.traceL_append e1,
      RunList.traceL_append (by rw [RunList.runL_single]; exact e2),
      RunList.traceL_append e3]
    have hq1 : BContrib [] (traceL (normal St.PRE none 0) sr.pre) := bcontrib_quiet q1
    have hq2 : BContrib [] (traceL (normal St.PRE none 0) [lbrace]) := by
      rw [RunList.traceL_single]; exact bcontrib_quiet (quiet_single q2)
    have hq4 : BContrib [] (traceL r3 sr.post) := bcontrib_quiet q4
    have := bcontrib_append hq1 (bcontrib_append hq2 (bcontrib_append k3 hq4))
    simpa using this

/-! ## From the list run to `Model.accepts` -/

theorem run_of_runL {bytes : ℕ → ℕ} {len : ℕ} : ∀ (n : ℕ), n ≤ len → ∀ {r : Regs},
    runL Regs.init (RunList.toL bytes n) = some r →
    (∀ i, i < n → (step (run bytes len i) (bytes i)).isSome) ∧ run bytes len n = r := by
  intro n
  induction n with
  | zero =>
    intro _ r h
    simp only [RunList.toL, List.range_zero, List.map_nil, RunList.runL_nil,
      Option.some.injEq] at h
    exact ⟨fun i hi => absurd hi (by omega), h⟩
  | succ n ih =>
    intro hn r h
    rw [RunList.toL_succ, RunList.runL_append] at h
    cases h1 : runL Regs.init (RunList.toL bytes n) with
    | none => rw [h1] at h; simp at h
    | some r1 =>
      rw [h1] at h
      simp only [Option.bind_some, RunList.runL_single] at h
      obtain ⟨ih1, ih2⟩ := ih (by omega) h1
      have hstep : step (run bytes len n) (bytes n) = some r := by rw [ih2]; exact h
      refine ⟨fun i hi => ?_, RunTheory.run_succ_of_step (by omega) hstep⟩
      rcases Nat.lt_or_ge i n with hlt | hge
      · exact ih1 i hlt
      · have : i = n := by omega
        subst this
        rw [hstep]; rfl

theorem bMatch_eq_filter (ms : List SMem) (k : Claim) :
    bMatch ms k = (ms.filter fun m => decide (m.claim = some k)).length := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [bMatch, List.map_cons, List.sum_cons, List.filter_cons]
    by_cases h : m.claim = some k <;> simp [h, ← ih, bMatch] <;> omega

/-- **Acceptance.** A well-formed serialization is accepted, and its read-outs
are the members' slots. -/
theorem ser_accepts {sr : Ser} (hwf : sr.WF) {bytes : ℕ → ℕ} {len : ℕ}
    (hb : RunList.toL bytes len = sr.bytes) :
    accepts bytes len = true ∧
      (∀ k : Claim, presentCount bytes len k = bMatch sr.body k) ∧
      (∀ k : Claim, slotLen bytes len k = (bVals sr.body k).length) ∧
      (∀ k : Claim, signCount bytes len k = bSign sr.body k) ∧
      (∀ k : Claim, trueCount bytes len k = bTrue sr.body k) ∧
      (∀ k : Claim, (Model.isStrClaim k = true ∨ Model.isIntClaim k = true) →
        ∀ t, cell bytes len k t = (bVals sr.body k).getD t 0) := by
  obtain ⟨r', hrun, hend, hsub, hnmem, hcon⟩ := ser_run (Ser.swf_of_wf hwf)
  rw [← hb] at hrun hcon
  obtain ⟨hsteps, hfin⟩ := run_of_runL len le_rfl hrun
  have hpres : ∀ k : Claim, presentCount bytes len k = bMatch sr.body k := by
    intro k
    rw [RunList.presentCount_eq hsteps k]
    exact hcon.1 k
  have hpres1 : ∀ k : Claim, presentCount bytes len k ≤ 1 := by
    intro k
    rw [hpres k, bMatch_eq_filter]
    exact hwf.2.2.2.2.2 k
  refine ⟨?_, hpres, ?_, ?_, ?_, ?_⟩
  · rw [RunList.accepts_iff]
    refine ⟨hsteps, ?_, ?_, ?_, hpres1⟩
    · rw [hfin]; exact hend
    · rw [hfin]; exact hsub
    · rw [hfin, hnmem]; exact hwf.2.2.2.2.1
  · intro k
    rw [RunList.slotLen_eq_valsT hsteps k, hcon.2.1 k]
  · intro k
    rw [RunList.signCount_eq hsteps k]
    exact hcon.2.2.1 k
  · intro k
    rw [RunList.trueCount_eq hsteps k]
    exact hcon.2.2.2 k
  · intro k hkind t
    rw [RunList.cell_eq_valsT k hkind hsteps (hpres1 k) t, hcon.2.1 k]

end SerRun

end Solution.JSONExtract
