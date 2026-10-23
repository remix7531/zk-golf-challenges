import Solution.JSONExtract.ModelBridge
import Solution.JSONExtract.MainTheorems
import Solution.JSONExtract.Anchors
import Solution.JSONExtract.Acceptance
import Solution.JSONExtract.LenFlags
import Solution.JSONExtract.SlotPins
import Solution.JSONExtract.MainEval

/-!
# The loop invariant of `Main.soundness` (`JSONExtract`)

Stated off the circuit: `Main.soundness` peels `main`'s spine, evaluates the
witness vectors it binds into the plain functions of `RunVals`, and hands the
gadget specifications to the theorems here.

The induction walks the 1024 positions once.  At position `i` the `*Prev` half
of the row encodes `Model.run bytes len i`, so `Step.Assumptions` holds there
and `Step.Spec` applies; the activity flag is the prefix sum of the length
one-hot, so the position is active exactly when `i < len`; an active position's
successor state vectors are the indicator vectors of the model's transitions,
and an all-zero one is refuted by the *next* position's one-hot row (or, at the
last position, by `Acceptance`).  So the transition exists, and the `*Next` half
encodes `Model.run bytes len (i + 1)`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSt nSub nClaims kIdxMax ofsMax St Sub Claim Regs)
open Witness (slots)

namespace MainSound

open Model (run step runSignals signals)

/-! ## The witnessed run as plain functions -/

/-- Everything `main` witnesses, read off the environment: one function per
register, indexed by position (and by state or claim for the one-hots). -/
structure RunVals where
  byteF : ℕ → F circomPrime
  lenFlagF : ℕ → F circomPrime
  accmF : ℕ → F circomPrime
  stF : ℕ → Fin nSt → F circomPrime
  subF : ℕ → Fin nSub → F circomPrime
  hexF : ℕ → F circomPrime
  kIdxF : ℕ → F circomPrime
  mF : ℕ → Fin nClaims → F circomPrime
  claimF : ℕ → Fin nClaims → F circomPrime
  ofsF : ℕ → F circomPrime
  nMemF : ℕ → F circomPrime
  sigF : ℕ → Step.Outputs (F circomPrime)
  outV : Output (F circomPrime)

/-- The `Step` input of position `i`. -/
def RunVals.row (R : RunVals) (i : ℕ) : Step.Inputs (F circomPrime) where
  byte := R.byteF i
  lenFlag := R.lenFlagF i
  accmPrev := R.accmF i
  accmNext := R.accmF (i + 1)
  stPrev := Vector.ofFn (R.stF i)
  stNext := Vector.ofFn (R.stF (i + 1))
  subPrev := Vector.ofFn (R.subF i)
  subNext := Vector.ofFn (R.subF (i + 1))
  hexAccPrev := R.hexF i
  hexAccNext := R.hexF (i + 1)
  kIdxPrev := R.kIdxF i
  kIdxNext := R.kIdxF (i + 1)
  mPrev := Vector.ofFn (R.mF i)
  mNext := Vector.ofFn (R.mF (i + 1))
  claimPrev := Vector.ofFn (R.claimF i)
  claimNext := Vector.ofFn (R.claimF (i + 1))
  ofsPrev := R.ofsF i
  ofsNext := R.ofsF (i + 1)
  nMemPrev := R.nMemF i
  nMemNext := R.nMemF (i + 1)
  out := R.outV

/-- Slot `i` of the witnessed run encodes the model registers `r`. -/
def Enc (R : RunVals) (i : ℕ) (r : Regs) : Prop :=
  (∀ j : Fin nSt, R.stF i j = if j = r.st then 1 else 0) ∧
  (∀ j : Fin nSub, R.subF i j = if j = r.sub then 1 else 0) ∧
  R.hexF i = (r.hexAcc : F circomPrime) ∧
  R.kIdxF i = (r.kIdx : F circomPrime) ∧
  (∀ k : Claim, R.mF i k = if r.m[k] then 1 else 0) ∧
  (∀ k : Claim, R.claimF i k = if r.claim = some k then 1 else 0) ∧
  R.ofsF i = (r.ofs : F circomPrime) ∧
  R.nMemF i = (r.nMem : F circomPrime)

theorem encodesPrev_iff (R : RunVals) (i : ℕ) (r : Regs) :
    Step.EncodesPrev (R.row i) r ↔ Enc R i r := by
  simp [Step.EncodesPrev, RunVals.row, Enc]

theorem encodesNext_iff (R : RunVals) (i : ℕ) (r : Regs) :
    Step.EncodesNext (R.row i) r ↔ Enc R (i + 1) r := by
  simp [Step.EncodesNext, RunVals.row, Enc]

/-! ## A one-hot with a known hit -/

theorem onehot_of_sum {n : ℕ} (hn : n < circomPrime) (v : Fin n → F circomPrime) (p : Fin n)
    (hb : ∀ j, IsBool (v j)) (hs : (∑ j, v j) = 1) (hp : v p = 1) :
    ∀ j, v j = if j = p then 1 else 0 := by
  have hcast : ((∑ j : Fin n, (v j).val : ℕ) : F circomPrime) = ∑ j : Fin n, v j := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun j _ => by rcases hb j with h | h <;> simp [h]
  have hle : (∑ j : Fin n, (v j).val) ≤ n := by
    have hb1 : ∀ j : Fin n, (v j).val ≤ 1 := fun j => by
      rcases hb j with h | h <;> simp [h, ZMod.val_one]
    calc (∑ j : Fin n, (v j).val) ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum fun j _ => hb1 j
      _ = n := by simp
  have hone : (∑ j : Fin n, (v j).val) = 1 := by
    have h1 : ((∑ j : Fin n, (v j).val : ℕ) : F circomPrime) = 1 := hcast.trans hs
    have h2 := congrArg ZMod.val h1
    rwa [ZMod.val_natCast_of_lt (lt_of_le_of_lt hle hn), ZMod.val_one] at h2
  have hpval : (v p).val = 1 := by rw [hp]; exact ZMod.val_one _
  intro j
  by_cases hj : j = p
  · rw [if_pos hj, hj, hp]
  · rw [if_neg hj]
    have hpair : (v j).val + (v p).val ≤ ∑ x : Fin n, (v x).val := by
      have hsub := Finset.sum_le_sum_of_subset
        (f := fun x : Fin n => (v x).val) (Finset.subset_univ ({j, p} : Finset (Fin n)))
      rwa [Finset.sum_pair hj] at hsub
    have hz : (v j).val = 0 := by omega
    rcases hb j with h | h
    · exact h
    · rw [h] at hz; simp [ZMod.val_one] at hz

/-! ## Projections of a row -/

@[simp] theorem row_byte (R : RunVals) (i : ℕ) : (R.row i).byte = R.byteF i := rfl
@[simp] theorem row_lenFlag (R : RunVals) (i : ℕ) : (R.row i).lenFlag = R.lenFlagF i := rfl
@[simp] theorem row_accmPrev (R : RunVals) (i : ℕ) : (R.row i).accmPrev = R.accmF i := rfl
@[simp] theorem row_accmNext (R : RunVals) (i : ℕ) : (R.row i).accmNext = R.accmF (i + 1) := rfl
@[simp] theorem row_hexPrev (R : RunVals) (i : ℕ) : (R.row i).hexAccPrev = R.hexF i := rfl
@[simp] theorem row_hexNext (R : RunVals) (i : ℕ) : (R.row i).hexAccNext = R.hexF (i + 1) := rfl
@[simp] theorem row_kIdxPrev (R : RunVals) (i : ℕ) : (R.row i).kIdxPrev = R.kIdxF i := rfl
@[simp] theorem row_kIdxNext (R : RunVals) (i : ℕ) : (R.row i).kIdxNext = R.kIdxF (i + 1) := rfl
@[simp] theorem row_ofsPrev (R : RunVals) (i : ℕ) : (R.row i).ofsPrev = R.ofsF i := rfl
@[simp] theorem row_ofsNext (R : RunVals) (i : ℕ) : (R.row i).ofsNext = R.ofsF (i + 1) := rfl
@[simp] theorem row_nMemPrev (R : RunVals) (i : ℕ) : (R.row i).nMemPrev = R.nMemF i := rfl
@[simp] theorem row_out (R : RunVals) (i : ℕ) : (R.row i).out = R.outV := rfl

@[simp] theorem row_stPrev (R : RunVals) (i : ℕ) (j : Fin nSt) :
    (R.row i).stPrev[j] = R.stF i j := by simp [RunVals.row]
@[simp] theorem row_stNext (R : RunVals) (i : ℕ) (j : Fin nSt) :
    (R.row i).stNext[j] = R.stF (i + 1) j := by simp [RunVals.row]
@[simp] theorem row_subPrev (R : RunVals) (i : ℕ) (j : Fin nSub) :
    (R.row i).subPrev[j] = R.subF i j := by simp [RunVals.row]
@[simp] theorem row_subNext (R : RunVals) (i : ℕ) (j : Fin nSub) :
    (R.row i).subNext[j] = R.subF (i + 1) j := by simp [RunVals.row]

/-! ## What `Main` supplies -/

/-- The gadget specifications of `main`, at the value level. -/
structure Rows (R : RunVals) (bytes : ℕ → ℕ) (len : ℕ) (d : ProverData (F circomPrime)) :
    Prop where
  byteVal : ∀ i, i < bufferLen → (R.byteF i).val = bytes i
  byteLt : ∀ i, bytes i < 256
  lenLe : len ≤ bufferLen
  lenFlag : ∀ i, i < bufferLen → R.lenFlagF i = if i = len then 1 else 0
  accm0 : R.accmF 0 = 0
  stPre : R.stF 0 St.PRE = 1
  subPlain : R.subF 0 Sub.PLAIN = 1
  hex0 : R.hexF 0 = 0
  kIdx0 : R.kIdxF 0 = 0
  ofs0 : R.ofsF 0 = 0
  nMem0 : R.nMemF 0 = 0
  m0 : ∀ k : Claim, R.mF 0 k = 0
  claim0 : ∀ k : Claim, R.claimF 0 k = 0
  stepSpec : ∀ i : Fin bufferLen,
    Step.Assumptions (R.row i.val) d → Step.Spec (R.row i.val) (R.sigF i.val) d
  endSt : R.stF bufferLen St.END = 1
  endSub : R.subF bufferLen Sub.PLAIN = 1
  memCap : (R.nMemF bufferLen).val ≤ Model.maxMembers

variable {R : RunVals} {bytes : ℕ → ℕ} {len : ℕ} {d : ProverData (F circomPrime)}

theorem val_cast_lt {m : ℕ} (h : m < circomPrime) : ((m : ℕ) : F circomPrime).val = m :=
  ZMod.val_natCast_of_lt h

/-- `Step.Assumptions` at a position whose `*Prev` half encodes the run. -/
theorem assumptions_of_enc (H : Rows R bytes len d) {i : ℕ} (hi : i < bufferLen)
    (henc : Enc R i (run bytes len i)) : Step.Assumptions (R.row i) d := by
  have hp : (4096 : ℕ) < circomPrime := by decide
  have hhex := IR.run_hexAcc_lt bytes len i
  have hkidx := IR.run_kIdx_le bytes len i
  have hofs := IR.run_ofs_le bytes len i
  simp only [Model.kIdxMax] at hkidx
  simp only [Model.ofsMax] at hofs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [row_byte, H.byteVal i hi]; exact H.byteLt i
  · rw [row_hexPrev, henc.2.2.1,
      val_cast_lt (show (run bytes len i).hexAcc < circomPrime by omega)]
    exact hhex
  · rw [row_kIdxPrev, henc.2.2.2.1,
      val_cast_lt (show (run bytes len i).kIdx < circomPrime by omega)]
    simp only [Model.kIdxMax]; omega
  · rw [row_ofsPrev, henc.2.2.2.2.2.2.1,
      val_cast_lt (show (run bytes len i).ofs < circomPrime by omega)]
    simp only [Model.ofsMax]; omega

/-- An all-zero state vector is refuted by the next position's one-hot row, or,
at the last slot, by `Acceptance`. -/
theorem not_all_zero_st (H : Rows R bytes len d) {m : ℕ} (hm : m ≤ bufferLen)
    (hb : (R.hexF m).val < 4096 ∧ (R.kIdxF m).val < kIdxMax ∧ (R.ofsF m).val < ofsMax) :
    ¬ (∀ j : Fin nSt, R.stF m j = 0) := by
  intro hz
  rcases Nat.lt_or_ge m bufferLen with h | h
  · have hA : Step.Assumptions (R.row m) d :=
      ⟨by rw [row_byte, H.byteVal m h]; exact H.byteLt m, hb.1, hb.2.1, hb.2.2⟩
    have hs := (H.stepSpec ⟨m, h⟩ hA).2.1
    have hzero : ∀ j : Fin nSt, (R.row m).stPrev[j] = (0 : F circomPrime) := fun j => by
      rw [row_stPrev]; exact hz j
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hzero j),
      Finset.sum_const_zero] at hs
    exact zero_ne_one hs
  · have hmb : m = bufferLen := by omega
    subst hmb
    have := hz St.END
    rw [H.endSt] at this
    exact one_ne_zero this

theorem not_all_zero_sub (H : Rows R bytes len d) {m : ℕ} (hm : m ≤ bufferLen)
    (hb : (R.hexF m).val < 4096 ∧ (R.kIdxF m).val < kIdxMax ∧ (R.ofsF m).val < ofsMax) :
    ¬ (∀ j : Fin nSub, R.subF m j = 0) := by
  intro hz
  rcases Nat.lt_or_ge m bufferLen with h | h
  · have hA : Step.Assumptions (R.row m) d :=
      ⟨by rw [row_byte, H.byteVal m h]; exact H.byteLt m, hb.1, hb.2.1, hb.2.2⟩
    have hs := (H.stepSpec ⟨m, h⟩ hA).2.2.2.1
    have hzero : ∀ j : Fin nSub, (R.row m).subPrev[j] = (0 : F circomPrime) := fun j => by
      rw [row_subPrev]; exact hz j
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hzero j),
      Finset.sum_const_zero] at hs
    exact zero_ne_one hs
  · have hmb : m = bufferLen := by omega
    subst hmb
    have := hz Sub.PLAIN
    rw [H.endSub] at this
    exact one_ne_zero this

set_option maxHeartbeats 1000000 in
/-- **The loop invariant.** -/
theorem invariant (H : Rows R bytes len d) :
    ∀ i, i ≤ bufferLen →
      Enc R i (run bytes len i) ∧ R.accmF i = (if len < i then 1 else 0) ∧
        (∀ j, j < i → j < len → (step (run bytes len j) (bytes j)).isSome) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hA : Step.Assumptions (R.row 0) d := by
      refine ⟨by rw [row_byte, H.byteVal 0 (by decide)]; exact H.byteLt 0, ?_, ?_, ?_⟩
      · rw [row_hexPrev, H.hex0]; simpa using (by decide : (0 : ℕ) < 4096)
      · rw [row_kIdxPrev, H.kIdx0]; simpa using (by decide : (0 : ℕ) < kIdxMax)
      · rw [row_ofsPrev, H.ofs0]; simpa using (by decide : (0 : ℕ) < ofsMax)
    obtain ⟨hstB, hstS, hsubB, hsubS, -⟩ := H.stepSpec ⟨0, by decide⟩ hA
    have hinit : run bytes len 0 = Model.Regs.init := rfl
    have hstB' : ∀ j : Fin nSt, IsBool (R.stF 0 j) := fun j => by
      have h := hstB j; rw [row_stPrev] at h; exact h
    have hstS' : (∑ j : Fin nSt, R.stF 0 j) = 1 := by
      rw [← hstS]; exact Finset.sum_congr rfl fun j _ => (row_stPrev R 0 j).symm
    have hsubB' : ∀ j : Fin nSub, IsBool (R.subF 0 j) := fun j => by
      have h := hsubB j; rw [row_subPrev] at h; exact h
    have hsubS' : (∑ j : Fin nSub, R.subF 0 j) = 1 := by
      rw [← hsubS]; exact Finset.sum_congr rfl fun j _ => (row_subPrev R 0 j).symm
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hinit]
      exact onehot_of_sum (by decide) (fun j => R.stF 0 j) St.PRE hstB' hstS' H.stPre
    · rw [hinit]
      exact onehot_of_sum (by decide) (fun j => R.subF 0 j) Sub.PLAIN hsubB' hsubS' H.subPlain
    · rw [H.hex0, hinit]; simp [Model.Regs.init]
    · rw [H.kIdx0, hinit]; simp [Model.Regs.init]
    · intro k; rw [H.m0 k, hinit]; simp [Model.Regs.init]
    · intro k; rw [H.claim0 k, hinit]; simp [Model.Regs.init]
    · rw [H.ofs0, hinit]; simp [Model.Regs.init]
    · rw [H.nMem0, hinit]; simp [Model.Regs.init]
    · rw [H.accm0, if_neg (by omega)]
    · intro j hj; omega
  | succ i ih =>
    intro hle
    have hi : i < bufferLen := by omega
    obtain ⟨henc, haccm, hstepsOK⟩ := ih (by omega)
    have hA := assumptions_of_enc H hi henc
    have hso := (H.stepSpec ⟨i, hi⟩ hA).2.2.2.2 (run bytes len i) (RunTheory.run_wf bytes len i)
      ((encodesPrev_iff R i _).mpr henc)
    have hbv : (R.row i).byte.val = bytes i := H.byteVal i hi
    simp only [Step.SpecOf] at hso
    rw [hbv] at hso
    obtain ⟨hAccmRow, hFrozen, hActive⟩ := hso
    have haccm' : R.accmF (i + 1) = (if len < i + 1 then 1 else 0) := by
      have : R.accmF (i + 1) = R.accmF i + R.lenFlagF i := hAccmRow
      rw [this, haccm, H.lenFlag i hi]
      by_cases h1 : len < i
      · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]; ring
      · rw [if_neg h1]
        by_cases h2 : i = len
        · rw [if_pos h2, if_pos (by omega)]; ring
        · rw [if_neg h2, if_neg (by omega)]; ring
    by_cases hact : i < len
    · -- an active position takes the transition
      have h0 : R.accmF (i + 1) = 0 := by rw [haccm', if_neg (by omega)]
      obtain ⟨hstN, hsubN, hhexB, hkidxB, hofsB, himp, hnext⟩ := hActive h0
      have hbnd : (R.hexF (i + 1)).val < 4096 ∧ (R.kIdxF (i + 1)).val < kIdxMax
          ∧ (R.ofsF (i + 1)).val < ofsMax := ⟨hhexB, hkidxB, hofsB⟩
      have hstSome : (Model.stepSt (Model.kindOf (run bytes len i).claim)
          (decide ((run bytes len i).sub = Sub.PLAIN)) (run bytes len i).st (bytes i)).isSome := by
        cases hsome : (Model.stepSt (Model.kindOf (run bytes len i).claim)
            (decide ((run bytes len i).sub = Sub.PLAIN)) (run bytes len i).st (bytes i)) with
        | none =>
          exfalso
          refine not_all_zero_st H (show i + 1 ≤ bufferLen by omega) hbnd (fun j => ?_)
          have hj := hstN j
          rw [row_stNext, hsome] at hj
          simpa using hj
        | some st' => rfl
      have hsubSome : (Model.stepSub (Model.inStr (run bytes len i).st) (run bytes len i).sub
          (bytes i)).isSome := by
        cases hsome : (Model.stepSub (Model.inStr (run bytes len i).st) (run bytes len i).sub
            (bytes i)) with
        | none =>
          exfalso
          refine not_all_zero_sub H (show i + 1 ≤ bufferLen by omega) hbnd (fun j => ?_)
          have hj := hsubN j
          rw [row_subNext, hsome] at hj
          simpa using hj
        | some sub' => rfl
      obtain ⟨r', hstep'⟩ := Option.isSome_iff_exists.mp (himp hsubSome hstSome)
      have hrun : run bytes len (i + 1) = r' := RunTheory.run_succ_of_step hact hstep'
      refine ⟨?_, haccm', ?_⟩
      · rw [hrun]
        exact (encodesNext_iff R i r').mp (hnext r' hstep').1
      · intro j hj _
        rcases Nat.lt_or_ge j i with h | h
        · exact hstepsOK j h (by omega)
        · have : j = i := by omega
          subst this
          exact Option.isSome_iff_exists.mpr ⟨r', hstep'⟩
    · -- a frozen position keeps everything
      have h1 : R.accmF (i + 1) = 1 := by rw [haccm', if_pos (by omega)]
      have hfr := (hFrozen h1).1
      refine ⟨?_, haccm', ?_⟩
      · rw [show run bytes len (i + 1) = run bytes len i from by
          rw [RunTheory.run_succ, if_neg hact]]
        exact (encodesNext_iff R i _).mp hfr
      · intro j hj hjl
        exact hstepsOK j (by omega) hjl

/-! ## From the invariant to acceptance and the slots -/

section Consequences

variable {R : RunVals} {bytes : ℕ → ℕ} {len : ℕ} {d : ProverData (F circomPrime)}

/-- The signals the circuit computes at position `i`: the run's signals at an
active position, the frozen position's at an inactive one. -/
def sigAt (bytes : ℕ → ℕ) (len i : ℕ) : Model.Signals :=
  if i < len then signals (run bytes len i) (bytes i) (run bytes len (i + 1)).st
  else signals (run bytes len i) (bytes i) (run bytes len i).st

theorem steps_some (H : Rows R bytes len d) {i : ℕ} (hi : i < len) :
    (step (run bytes len i) (bytes i)).isSome :=
  (invariant H bufferLen le_rfl).2.2 i (by have := H.lenLe; omega) hi

theorem sigAt_lt {i : ℕ} (hi : i < len) : sigAt bytes len i = runSignals bytes len i := by
  rw [sigAt, if_pos hi, RunTheory.run_succ, if_pos hi]
  simp only [Model.runSignals, if_pos hi]

/-- Past `len` the run sits in `END`, where the four signals the end pins read
are off -- just as they are in `Model.runSignals`. -/
theorem sigAt_ge (hend : (run bytes len len).st = St.END) {i : ℕ} (hi : len ≤ i) :
    (∀ k : Claim, (sigAt bytes len i).match_[k] = false) ∧
    (sigAt bytes len i).vEmit = false ∧
    (sigAt bytes len i).minusFlag = false ∧
    (sigAt bytes len i).trueDone = false := by
  have hrun : run bytes len i = run bytes len len := RunTheory.run_frozen bytes len i hi
  have hst : (run bytes len i).st = St.END := by rw [hrun]; exact hend
  obtain ⟨hm, hv, -, hmf, htd⟩ := RunTheory.signals_end (run bytes len i) (bytes i) hst
  rw [sigAt, if_neg (by omega)]
  exact ⟨hm, hv, hmf, htd⟩

theorem runSignals_ge {i : ℕ} (hi : len ≤ i) :
    (∀ k : Claim, (runSignals bytes len i).match_[k] = false) ∧
    (runSignals bytes len i).vEmit = false ∧
    (runSignals bytes len i).minusFlag = false ∧
    (runSignals bytes len i).trueDone = false := by
  simp [Model.runSignals, Nat.not_lt.mpr hi]

/-- The per-position signals the end pins consume, read against the model. -/
theorem outSignals_at (H : Rows R bytes len d) {i : ℕ} (hi : i < bufferLen) :
    Step.OutSignals (R.sigF i) (run bytes len i) (sigAt bytes len i) := by
  obtain ⟨henc, -, -⟩ := invariant H i (by omega)
  obtain ⟨-, haccm', -⟩ := invariant H (i + 1) (by omega)
  have hA := assumptions_of_enc H hi henc
  have hso := (H.stepSpec ⟨i, hi⟩ hA).2.2.2.2 (run bytes len i) (RunTheory.run_wf bytes len i)
    ((encodesPrev_iff R i _).mpr henc)
  have hbv : (R.row i).byte.val = bytes i := H.byteVal i hi
  simp only [Step.SpecOf] at hso
  rw [hbv] at hso
  obtain ⟨-, hFrozen, hActive⟩ := hso
  by_cases hact : i < len
  · have h0 : R.accmF (i + 1) = 0 := by rw [haccm', if_neg (by omega)]
    obtain ⟨-, -, -, -, -, -, hnext⟩ := hActive h0
    obtain ⟨r', hstep'⟩ := Option.isSome_iff_exists.mp (steps_some H hact)
    have hrun : run bytes len (i + 1) = r' := RunTheory.run_succ_of_step hact hstep'
    rw [sigAt, if_pos hact, hrun]
    exact (hnext r' hstep').2.1
  · have h1 : R.accmF (i + 1) = 1 := by rw [haccm', if_pos (by omega)]
    rw [sigAt, if_neg hact]
    exact (hFrozen h1).2

/-! ### The four end sums -/

theorem sum_ind_eq_count (p : ℕ → Bool) : ∀ N : ℕ,
    (∑ i : Fin N, (if p i.val = true then (1 : F circomPrime) else 0))
      = (((List.range N).filter p).length : F circomPrime) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    simp only [List.range_succ, List.filter_append, List.length_append, List.filter_cons,
      List.filter_nil]
    by_cases h : p N = true <;> simp [h]

/-- The frozen tail contributes nothing to a count over the whole buffer. -/
theorem count_trunc (p : ℕ → Bool) (hlen : len ≤ bufferLen)
    (h : ∀ i, len ≤ i → p i = false) :
    (((List.range bufferLen).filter p).length : F circomPrime)
      = (((List.range len).filter p).length : F circomPrime) := by
  rw [IR.filter_range_trunc p hlen h]

theorem ite_and_eq (b : Bool) (P : Prop) [Decidable P] :
    (if b = true ∧ P then (1 : F circomPrime) else 0) = if (b && decide P) = true then 1 else 0 := by
  by_cases hb : b = true <;> by_cases hp : P <;> simp [hb, hp]

/-- The presence sum counts the members keyed `k`. -/
theorem presentSum_eq (H : Rows R bytes len d) (hend : (run bytes len len).st = St.END)
    (k : Claim) :
    (∑ i : Fin bufferLen, (R.sigF i.val).match_[k])
      = ((Model.presentCount bytes len k : ℕ) : F circomPrime) := by
  have hterm : ∀ i : Fin bufferLen, (R.sigF i.val).match_[k]
      = if (runSignals bytes len i.val).match_[k] = true then (1 : F circomPrime) else 0 := by
    intro i
    rw [(outSignals_at H i.isLt).1 k]
    by_cases hi : i.val < len
    · rw [sigAt_lt hi]
    · rw [(sigAt_ge hend (Nat.not_lt.mp hi)).1 k, (runSignals_ge (Nat.not_lt.mp hi)).1 k]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
    sum_ind_eq_count (fun j => (runSignals bytes len j).match_[k]),
    count_trunc _ (H.lenLe) (fun i hi => (runSignals_ge hi).1 k)]
  rfl

/-- The length sum counts the values routed to `k`. -/
theorem lenSum_eq (H : Rows R bytes len d) (hend : (run bytes len len).st = St.END)
    (k : Claim) :
    (∑ i : Fin bufferLen, (R.sigF i.val).vEmitK[k])
      = ((Model.slotLen bytes len k : ℕ) : F circomPrime) := by
  have hterm : ∀ i : Fin bufferLen, (R.sigF i.val).vEmitK[k]
      = if ((runSignals bytes len i.val).vEmit
            && decide ((run bytes len i.val).claim = some k)) = true
        then (1 : F circomPrime) else 0 := by
    intro i
    rw [(outSignals_at H i.isLt).2.1 k, ite_and_eq]
    by_cases hi : i.val < len
    · rw [sigAt_lt hi]
    · rw [(sigAt_ge hend (Nat.not_lt.mp hi)).2.1, (runSignals_ge (Nat.not_lt.mp hi)).2.1]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
    sum_ind_eq_count (fun j => (runSignals bytes len j).vEmit
      && decide ((run bytes len j).claim = some k)),
    count_trunc _ (H.lenLe) (fun i hi => by
      rw [(runSignals_ge hi).2.1]; rfl)]
  rfl

/-- The sign sum counts the `-` consumed for `k`. -/
theorem negSum_eq (H : Rows R bytes len d) (hend : (run bytes len len).st = St.END)
    (k : Claim) :
    (∑ i : Fin bufferLen, (R.sigF i.val).minusK[k])
      = ((Model.signCount bytes len k : ℕ) : F circomPrime) := by
  have hterm : ∀ i : Fin bufferLen, (R.sigF i.val).minusK[k]
      = if ((runSignals bytes len i.val).minusFlag
            && decide ((run bytes len i.val).claim = some k)) = true
        then (1 : F circomPrime) else 0 := by
    intro i
    rw [(outSignals_at H i.isLt).2.2.1 k, ite_and_eq]
    by_cases hi : i.val < len
    · rw [sigAt_lt hi]
    · rw [(sigAt_ge hend (Nat.not_lt.mp hi)).2.2.1, (runSignals_ge (Nat.not_lt.mp hi)).2.2.1]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
    sum_ind_eq_count (fun j => (runSignals bytes len j).minusFlag
      && decide ((run bytes len j).claim = some k)),
    count_trunc _ (H.lenLe) (fun i hi => by
      rw [(runSignals_ge hi).2.2.1]; rfl)]
  rfl

/-- The `true` sum counts the completed `true` literals of the boolean claim. -/
theorem trueSum_eq (H : Rows R bytes len d) (hend : (run bytes len len).st = St.END) :
    (∑ i : Fin bufferLen, (R.sigF i.val).trueK)
      = ((Model.trueCount bytes len 6 : ℕ) : F circomPrime) := by
  have hterm : ∀ i : Fin bufferLen, (R.sigF i.val).trueK
      = if ((runSignals bytes len i.val).trueDone
            && decide ((run bytes len i.val).claim = some 6)) = true
        then (1 : F circomPrime) else 0 := by
    intro i
    rw [(outSignals_at H i.isLt).2.2.2, ite_and_eq]
    by_cases hi : i.val < len
    · rw [sigAt_lt hi]
    · rw [(sigAt_ge hend (Nat.not_lt.mp hi)).2.2.2, (runSignals_ge (Nat.not_lt.mp hi)).2.2.2]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
    sum_ind_eq_count (fun j => (runSignals bytes len j).trueDone
      && decide ((run bytes len j).claim = some 6)),
    count_trunc _ (H.lenLe) (fun i hi => by
      rw [(runSignals_ge hi).2.2.2]; rfl)]
  rfl

/-! ### Acceptance -/

theorem run_end (H : Rows R bytes len d) :
    (run bytes len len).st = St.END ∧ (run bytes len len).sub = Sub.PLAIN ∧
      (run bytes len len).nMem ≤ Model.maxMembers := by
  obtain ⟨henc, -, -⟩ := invariant H bufferLen le_rfl
  have hfr : run bytes len bufferLen = run bytes len len :=
    RunTheory.run_frozen bytes len bufferLen (H.lenLe)
  refine ⟨?_, ?_, ?_⟩
  · have h := henc.1 St.END
    rw [H.endSt] at h
    by_cases hq : St.END = (run bytes len bufferLen).st
    · rw [← hfr]; exact hq.symm
    · rw [if_neg hq] at h; exact absurd h one_ne_zero
  · have h := henc.2.1 Sub.PLAIN
    rw [H.endSub] at h
    by_cases hq : Sub.PLAIN = (run bytes len bufferLen).sub
    · rw [← hfr]; exact hq.symm
    · rw [if_neg hq] at h; exact absurd h one_ne_zero
  · have h := henc.2.2.2.2.2.2.2
    have hnm := IR.run_nMem_le bytes len bufferLen
    have hp : (run bytes len bufferLen).nMem < circomPrime := by
      have h2 : (bufferLen : ℕ) < circomPrime := by decide
      omega
    have hcap := H.memCap
    rw [h, val_cast_lt hp, hfr] at hcap
    exact hcap

theorem presentCount_le_one (H : Rows R bytes len d) (hend : (run bytes len len).st = St.END)
    (k : Claim) (hbool : IsBool (∑ i : Fin bufferLen, (R.sigF i.val).match_[k])) :
    Model.presentCount bytes len k ≤ 1 := by
  rw [presentSum_eq H hend k] at hbool
  have hle := RunTheory.presentCount_le bytes len k
  have hp : Model.presentCount bytes len k < circomPrime := by
    have hl := H.lenLe
    have h2 : (bufferLen : ℕ) < circomPrime := by decide
    omega
  rcases hbool with h | h
  · have h2 := congrArg ZMod.val h
    rw [val_cast_lt hp, ZMod.val_zero] at h2; omega
  · have h2 := congrArg ZMod.val h
    rw [val_cast_lt hp, ZMod.val_one] at h2; omega

theorem accepts_of_rows (H : Rows R bytes len d)
    (hbool : ∀ k : Claim, IsBool (∑ i : Fin bufferLen, (R.sigF i.val).match_[k])) :
    Model.accepts bytes len = true := by
  obtain ⟨hst, hsub, hmem⟩ := run_end H
  rw [ModelBridge.accepts_iff]
  exact ⟨fun i hi => steps_some H hi, hst, hsub, hmem,
    fun k => presentCount_le_one H hst k (hbool k)⟩

/-! ### The routed cells -/

/-- The write row of an active position. -/
theorem writesCell_at (H : Rows R bytes len d) {i : ℕ} (hi : i < len) :
    Step.WritesCell (R.row i) (run bytes len i) (sigAt bytes len i) := by
  have hib : i < bufferLen := by have := H.lenLe; omega
  obtain ⟨henc, -, -⟩ := invariant H i (by omega)
  obtain ⟨-, haccm', -⟩ := invariant H (i + 1) (by omega)
  have hA := assumptions_of_enc H hib henc
  have hso := (H.stepSpec ⟨i, hib⟩ hA).2.2.2.2 (run bytes len i) (RunTheory.run_wf bytes len i)
    ((encodesPrev_iff R i _).mpr henc)
  have hbv : (R.row i).byte.val = bytes i := H.byteVal i hib
  simp only [Step.SpecOf] at hso
  rw [hbv] at hso
  obtain ⟨-, -, hActive⟩ := hso
  have h0 : R.accmF (i + 1) = 0 := by rw [haccm', if_neg (by omega)]
  obtain ⟨-, -, -, -, -, -, hnext⟩ := hActive h0
  obtain ⟨r', hstep'⟩ := Option.isSome_iff_exists.mp (steps_some H hi)
  have hrun : run bytes len (i + 1) = r' := RunTheory.run_succ_of_step hi hstep'
  rw [sigAt, if_pos hi, hrun]
  exact (hnext r' hstep').2.2

theorem cell_val (H : Rows R bytes len d) (hend : (run bytes len len).st = St.END)
    (k : Claim) (hkind : Model.isStrClaim k = true ∨ Model.isIntClaim k = true)
    (hpres : Model.presentCount bytes len k ≤ 1) {t : ℕ}
    (hzero : Model.slotLen bytes len k ≤ t → Step.outCell R.outV k t = 0) :
    Step.outCell R.outV k t = ((Model.cell bytes len k t : ℕ) : F circomPrime) := by
  have hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome :=
    fun i h => steps_some H h
  by_cases ht : t < Model.slotLen bytes len k
  · obtain ⟨i, hi, hei, hofs⟩ := RunTheory.cover bytes len k hkind hsteps hpres ht
    have hei' := hei
    simp only [RunTheory.emitsAt, Bool.and_eq_true, decide_eq_true_eq] at hei'
    obtain ⟨hv, hcl⟩ := hei'
    have hw : (runSignals bytes len i).write = true := by
      rw [RunTheory.write_eq_vEmit bytes len k hkind hcl]; exact hv
    have hwc := writesCell_at H hi k (by rw [sigAt_lt hi]; exact hw) hcl
    rw [sigAt_lt hi, row_out, hofs] at hwc
    rw [hwc, ← hofs, RunTheory.cell_eq_valOut bytes len k hkind hsteps hpres hi hei]
  · push_neg at ht
    rw [hzero ht, RunTheory.cell_eq_zero bytes len k hkind hsteps hpres ht]
    simp

/-! ### The slots -/

theorem outCell_getElem {n : ℕ} (v : Vector (F circomPrime) n) (t : ℕ) (ht : t < n) :
    v[t]?.getD 0 = v[t] := by
  rw [Vector.getElem?_eq_getElem ht]; rfl

/-- The sums of the per-position signals that the end pins consume. -/
def RunVals.presentSum (R : RunVals) (k : Claim) : F circomPrime :=
  ∑ i : Fin bufferLen, (R.sigF i.val).match_[k]

def RunVals.lenSum (R : RunVals) (k : Claim) : F circomPrime :=
  ∑ i : Fin bufferLen, (R.sigF i.val).vEmitK[k]

def RunVals.negSum (R : RunVals) (k : Claim) : F circomPrime :=
  ∑ i : Fin bufferLen, (R.sigF i.val).minusK[k]

def RunVals.trueSum (R : RunVals) : F circomPrime :=
  ∑ i : Fin bufferLen, (R.sigF i.val).trueK

theorem countLt (H : Rows R bytes len d) {m : ℕ} (h : m ≤ len) : m < circomPrime := by
  have hl := H.lenLe
  have h2 : (bufferLen : ℕ) < circomPrime := by decide
  omega

/-- A string slot of the circuit output is the model's string slot. -/
theorem strSlot_eq (H : Rows R bytes len d) (hend : (run bytes len len).st = St.END)
    (k : Claim) (n : ℕ) (slot : StrSlot n (F circomPrime))
    (hkind : Model.isStrClaim k = true ∨ Model.isIntClaim k = true)
    (hpres : Model.presentCount bytes len k ≤ 1)
    (hout : ∀ (t : ℕ) (ht : t < n), Step.outCell R.outV k t = slot.bytes[t])
    (hpin : StrSlotPin.Spec n ⟨slot, R.presentSum k, R.lenSum k⟩) :
    strSlotToNats slot = ModelBridge.expectedStr bytes len k n := by
  obtain ⟨-, hpresEq, hlenEq, hfit, hz⟩ := hpin
  simp only at hpresEq hlenEq hfit hz
  rw [RunVals.presentSum, presentSum_eq H hend k] at hpresEq
  rw [RunVals.lenSum, lenSum_eq H hend k] at hlenEq hfit hz
  rw [val_cast_lt (countLt H (RunTheory.slotLen_le bytes len k))] at hfit hz
  have h1 : slot.present.val = Model.presentCount bytes len k := by
    rw [hpresEq, val_cast_lt (countLt H (RunTheory.presentCount_le bytes len k))]
  have h2 : slot.len.val = Model.slotLen bytes len k := by
    rw [hlenEq, val_cast_lt (countLt H (RunTheory.slotLen_le bytes len k))]
  have h3 : slot.bytes.map ZMod.val
      = Vector.ofFn fun t : Fin n => Model.cell bytes len k t.val := by
    apply Vector.ext
    intro t htlt
    rw [Vector.getElem_map, Vector.getElem_ofFn]
    have hc := cell_val H hend k hkind hpres (t := t) (fun hle => by
      rw [hout t htlt]
      exact hz ⟨t, htlt⟩ hle)
    rw [hout t htlt] at hc
    rw [hc, val_cast_lt (by
      have := RunTheory.cell_lt bytes len k t H.byteLt
      have h2 : (65536 : ℕ) < circomPrime := by decide
      omega)]
  unfold strSlotToNats ModelBridge.expectedStr
  rw [h1, h2, h3]

/-- An integer slot of the circuit output is the model's integer slot. -/
theorem intSlot_eq (H : Rows R bytes len d) (hend : (run bytes len len).st = St.END)
    (k : Claim) (n : ℕ) (slot : IntSlot n (F circomPrime))
    (hkind : Model.isStrClaim k = true ∨ Model.isIntClaim k = true)
    (hpres : Model.presentCount bytes len k ≤ 1)
    (hout : ∀ (t : ℕ) (ht : t < n), Step.outCell R.outV k t = slot.digits[t])
    (hpin : IntSlotPin.Spec n ⟨slot, R.presentSum k, R.negSum k, R.lenSum k⟩) :
    intSlotToNats slot = ModelBridge.expectedInt bytes len k n := by
  obtain ⟨-, hpresEq, hnegEq, hlenEq, hfit, hz⟩ := hpin
  simp only at hpresEq hnegEq hlenEq hfit hz
  rw [RunVals.presentSum, presentSum_eq H hend k] at hpresEq
  rw [RunVals.negSum, negSum_eq H hend k] at hnegEq
  rw [RunVals.lenSum, lenSum_eq H hend k] at hlenEq hfit hz
  rw [val_cast_lt (countLt H (RunTheory.slotLen_le bytes len k))] at hfit hz
  have h1 : slot.present.val = Model.presentCount bytes len k := by
    rw [hpresEq, val_cast_lt (countLt H (RunTheory.presentCount_le bytes len k))]
  have h1' : slot.negative.val = Model.signCount bytes len k := by
    rw [hnegEq, val_cast_lt (countLt H (RunTheory.signCount_le bytes len k))]
  have h2 : slot.len.val = Model.slotLen bytes len k := by
    rw [hlenEq, val_cast_lt (countLt H (RunTheory.slotLen_le bytes len k))]
  have h3 : slot.digits.map ZMod.val
      = Vector.ofFn fun t : Fin n => Model.cell bytes len k t.val := by
    apply Vector.ext
    intro t htlt
    rw [Vector.getElem_map, Vector.getElem_ofFn]
    have hc := cell_val H hend k hkind hpres (t := t) (fun hle => by
      rw [hout t htlt]
      exact hz ⟨t, htlt⟩ hle)
    rw [hout t htlt] at hc
    rw [hc, val_cast_lt (by
      have := RunTheory.cell_lt bytes len k t H.byteLt
      have h2 : (65536 : ℕ) < circomPrime := by decide
      omega)]
  unfold intSlotToNats ModelBridge.expectedInt
  rw [h1, h1', h2, h3]

/-- The boolean slot of the circuit output is the model's boolean slot. -/
theorem boolSlot_eq (H : Rows R bytes len d) (hend : (run bytes len len).st = St.END)
    (slot : BoolSlot (F circomPrime))
    (hpin : BoolSlotPin.Spec ⟨slot, R.presentSum 6, R.trueSum⟩) :
    boolSlotToNats slot = ModelBridge.expectedBool bytes len 6 := by
  obtain ⟨-, hpresEq, hvalEq⟩ := hpin
  simp only at hpresEq hvalEq
  rw [RunVals.presentSum, presentSum_eq H hend 6] at hpresEq
  rw [RunVals.trueSum, trueSum_eq H hend] at hvalEq
  unfold boolSlotToNats ModelBridge.expectedBool
  rw [hpresEq, hvalEq, val_cast_lt (countLt H (RunTheory.presentCount_le bytes len 6)),
    val_cast_lt (countLt H (RunTheory.trueCount_le bytes len 6))]

/-! ## The top-level statement, off the circuit -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **From the rows of `main` to the model.**  The witnessed run is the honest
run, it accepts, and the output slots are the model's read-outs. -/
theorem spec_of_rows (H : Rows R bytes len d)
    (hiss : StrSlotPin.Spec _ ⟨R.outV.iss, R.presentSum 0, R.lenSum 0⟩)
    (hsub : StrSlotPin.Spec _ ⟨R.outV.sub, R.presentSum 1, R.lenSum 1⟩)
    (haud : StrSlotPin.Spec _ ⟨R.outV.aud, R.presentSum 2, R.lenSum 2⟩)
    (hazp : StrSlotPin.Spec _ ⟨R.outV.azp, R.presentSum 3, R.lenSum 3⟩)
    (hhd : StrSlotPin.Spec _ ⟨R.outV.hd, R.presentSum 4, R.lenSum 4⟩)
    (hemail : StrSlotPin.Spec _ ⟨R.outV.email, R.presentSum 5, R.lenSum 5⟩)
    (hev : BoolSlotPin.Spec ⟨R.outV.emailVerified, R.presentSum 6, R.trueSum⟩)
    (hnonce : StrSlotPin.Spec _ ⟨R.outV.nonce, R.presentSum 7, R.lenSum 7⟩)
    (hatHash : StrSlotPin.Spec _ ⟨R.outV.atHash, R.presentSum 8, R.lenSum 8⟩)
    (hiat : IntSlotPin.Spec _ ⟨R.outV.iat, R.presentSum 9, R.negSum 9, R.lenSum 9⟩)
    (hexp : IntSlotPin.Spec _ ⟨R.outV.exp, R.presentSum 10, R.negSum 10, R.lenSum 10⟩) :
    Model.accepts bytes len = true ∧
      outputToNats R.outV = ModelBridge.expected bytes len := by
  have hbool : ∀ k : Claim, IsBool (R.presentSum k) := by
    intro k
    fin_cases k
    exacts [hiss.1, hsub.1, haud.1, hazp.1, hhd.1, hemail.1, hev.1, hnonce.1, hatHash.1,
      hiat.1, hexp.1]
  have hacc : Model.accepts bytes len = true := accepts_of_rows H hbool
  obtain ⟨hend, -, -⟩ := run_end H
  have hpres : ∀ k : Claim, Model.presentCount bytes len k ≤ 1 :=
    fun k => presentCount_le_one H hend k (hbool k)
  refine ⟨hacc, ?_⟩
  have e0 := strSlot_eq H hend 0 _ R.outV.iss (by decide) (hpres 0)
    (fun t ht => outCell_getElem _ t ht) hiss
  have e1 := strSlot_eq H hend 1 _ R.outV.sub (by decide) (hpres 1)
    (fun t ht => outCell_getElem _ t ht) hsub
  have e2 := strSlot_eq H hend 2 _ R.outV.aud (by decide) (hpres 2)
    (fun t ht => outCell_getElem _ t ht) haud
  have e3 := strSlot_eq H hend 3 _ R.outV.azp (by decide) (hpres 3)
    (fun t ht => outCell_getElem _ t ht) hazp
  have e4 := strSlot_eq H hend 4 _ R.outV.hd (by decide) (hpres 4)
    (fun t ht => outCell_getElem _ t ht) hhd
  have e5 := strSlot_eq H hend 5 _ R.outV.email (by decide) (hpres 5)
    (fun t ht => outCell_getElem _ t ht) hemail
  have e6 := boolSlot_eq H hend R.outV.emailVerified hev
  have e7 := strSlot_eq H hend 7 _ R.outV.nonce (by decide) (hpres 7)
    (fun t ht => outCell_getElem _ t ht) hnonce
  have e8 := strSlot_eq H hend 8 _ R.outV.atHash (by decide) (hpres 8)
    (fun t ht => outCell_getElem _ t ht) hatHash
  have e9 := intSlot_eq H hend 9 _ R.outV.iat (by decide) (hpres 9)
    (fun t ht => outCell_getElem _ t ht) hiat
  have e10 := intSlot_eq H hend 10 _ R.outV.exp (by decide) (hpres 10)
    (fun t ht => outCell_getElem _ t ht) hexp
  unfold outputToNats ModelBridge.expected
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]

end Consequences

/-! ## Reading `RunVals` off `main`'s witness vectors -/

section OfVectors

theorem gd {α : Type} {n : ℕ} (v : Vector α n) (i : ℕ) (h : i < n) (a : α) :
    v[i]?.getD a = v[i] := by
  rw [Vector.getElem?_eq_getElem h]; rfl

/-- The `RunVals` of `main`'s witness vectors under an environment. -/
def ofVectors (env : Environment (F circomPrime))
    (buffer : Vector E bufferLen) (lenFlags : Vector E slots)
    (accm hexAcc kIdx ofs nMem : Vector E slots)
    (st : Vector E (nSt * slots)) (sub : Vector E (nSub * slots))
    (m claim : Vector E (nClaims * slots))
    (sigs : Vector (Var Step.Outputs (F circomPrime)) bufferLen)
    (out : Var Output (F circomPrime)) : RunVals where
  byteF i := Expression.eval env (buffer[i]?.getD 0)
  lenFlagF i := Expression.eval env (lenFlags[i]?.getD 0)
  accmF i := Expression.eval env (accm[i]?.getD 0)
  stF i j := Expression.eval env (st[i * nSt + j.val]?.getD 0)
  subF i j := Expression.eval env (sub[i * nSub + j.val]?.getD 0)
  hexF i := Expression.eval env (hexAcc[i]?.getD 0)
  kIdxF i := Expression.eval env (kIdx[i]?.getD 0)
  mF i k := Expression.eval env (m[i * nClaims + k.val]?.getD 0)
  claimF i k := Expression.eval env (claim[i * nClaims + k.val]?.getD 0)
  ofsF i := Expression.eval env (ofs[i]?.getD 0)
  nMemF i := Expression.eval env (nMem[i]?.getD 0)
  sigF i := if h : i < bufferLen then eval env (sigs[i]'h) else eval env (sigs[0]'(by decide))
  outV := eval env out

variable (env : Environment (F circomPrime))
  (buffer : Vector E bufferLen) (lenFlags : Vector E slots)
  (accm hexAcc kIdx ofs nMem : Vector E slots)
  (st : Vector E (nSt * slots)) (sub : Vector E (nSub * slots))
  (m claim : Vector E (nClaims * slots))
  (sigs : Vector (Var Step.Outputs (F circomPrime)) bufferLen)
  (out : Var Output (F circomPrime))

/-- A slice of a position-major register, evaluated. -/
theorem eval_sliceAt {n : ℕ} (v : Vector E (n * slots)) (i : ℕ) (hi : i < slots) :
    (eval env (sliceAt n v i hi) : Vector (F circomPrime) n)
      = Vector.ofFn fun s : Fin n => Expression.eval env (v[i * n + s.val]?.getD 0) := by
  rw [CircuitType.eval_var_fields]
  apply Vector.ext
  intro s hs
  rw [Vector.getElem_map, Vector.getElem_ofFn, sliceAt, Vector.getElem_ofFn, gd]

set_option maxHeartbeats 1000000 in
theorem ofVectors_row (i : Fin bufferLen) (h1 : i.val < slots) (h2 : i.val + 1 < slots) :
    (ofVectors env buffer lenFlags accm hexAcc kIdx ofs nMem st sub m claim sigs out).row i.val
      = eval env
          ({ byte := buffer[i], lenFlag := prevAt lenFlags i,
             accmPrev := prevAt accm i, accmNext := nextAt accm i,
             stPrev := sliceAt nSt st i.val h1, stNext := sliceAt nSt st (i.val + 1) h2,
             subPrev := sliceAt nSub sub i.val h1, subNext := sliceAt nSub sub (i.val + 1) h2,
             hexAccPrev := prevAt hexAcc i, hexAccNext := nextAt hexAcc i,
             kIdxPrev := prevAt kIdx i, kIdxNext := nextAt kIdx i,
             mPrev := sliceAt nClaims m i.val h1, mNext := sliceAt nClaims m (i.val + 1) h2,
             claimPrev := sliceAt nClaims claim i.val h1,
             claimNext := sliceAt nClaims claim (i.val + 1) h2,
             ofsPrev := prevAt ofs i, ofsNext := nextAt ofs i,
             nMemPrev := prevAt nMem i, nMemNext := nextAt nMem i,
             out := out } : Var Step.Inputs (F circomPrime)) := by
  have hib := i.isLt
  rw [eval_stepIn]
  unfold RunVals.row ofVectors
  refine Step.Inputs.mk.injEq .. ▸ ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [prevAt, nextAt, eval_sliceAt, gd _ _ i.isLt, gd _ _ h1, gd _ _ h2,
      Fin.getElem_fin]

theorem ofVectors_sigF (i : ℕ) (hi : i < bufferLen) :
    (ofVectors env buffer lenFlags accm hexAcc kIdx ofs nMem st sub m claim sigs out).sigF i
      = eval env (sigs[i]'hi) := dif_pos hi

/-! ### The end sums, read off the circuit -/

theorem ofVectors_presentSum (k : Claim) :
    (ofVectors env buffer lenFlags accm hexAcc kIdx ofs nMem st sub m claim sigs out).presentSum k
      = Expression.eval env (sumOver sigs fun s => s.match_[k]) := by
  rw [RunVals.presentSum, eval_sumOver]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [ofVectors, dif_pos i.isLt, eval_stepOut', Fin.getElem_fin, getElem_eval_vec]

theorem ofVectors_lenSum (k : Claim) :
    (ofVectors env buffer lenFlags accm hexAcc kIdx ofs nMem st sub m claim sigs out).lenSum k
      = Expression.eval env (sumOver sigs fun s => s.vEmitK[k]) := by
  rw [RunVals.lenSum, eval_sumOver]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [ofVectors, dif_pos i.isLt, eval_stepOut', Fin.getElem_fin, getElem_eval_vec]

theorem ofVectors_negSum (k : Claim) :
    (ofVectors env buffer lenFlags accm hexAcc kIdx ofs nMem st sub m claim sigs out).negSum k
      = Expression.eval env (sumOver sigs fun s => s.minusK[k]) := by
  rw [RunVals.negSum, eval_sumOver]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [ofVectors, dif_pos i.isLt, eval_stepOut', Fin.getElem_fin, getElem_eval_vec]

theorem ofVectors_trueSum :
    (ofVectors env buffer lenFlags accm hexAcc kIdx ofs nMem st sub m claim sigs out).trueSum
      = Expression.eval env (sumOver sigs fun s => s.trueK) := by
  rw [RunVals.trueSum, eval_sumOver]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [ofVectors, dif_pos i.isLt, eval_stepOut']

end OfVectors

/-! ## The parsed prefix -/

/-- The input buffer as a total byte function. -/
def bufBytes (buf : Vector (F circomPrime) bufferLen) : ℕ → ℕ :=
  fun j => if h : j < bufferLen then (buf[j]'h).val else 0

theorem bufBytes_lt (buf : Vector (F circomPrime) bufferLen) (i : ℕ) (h : i < bufferLen) :
    bufBytes buf i = (buf[i]'h).val := dif_pos h

theorem bufBytes_ge (buf : Vector (F circomPrime) bufferLen) (i : ℕ) (h : ¬ i < bufferLen) :
    bufBytes buf i = 0 := dif_neg h

theorem prefix_toList (buf : Vector (F circomPrime) bufferLen) (len : ℕ) (h : len ≤ bufferLen) :
    (Specs.JSONExtract.takePrefix (fieldElemsToNat buf) len h).toList
      = List.ofFn (fun i : Fin len => bufBytes buf i.val) := by
  rw [Specs.JSONExtract.takePrefix, Vector.toList_ofFn]
  congr 1
  funext i
  rw [fieldElemsToNat, Vector.getElem_map]
  simp only [bufBytes, dif_pos (lt_of_lt_of_le i.isLt h)]

/-- The trusted specification, from the bridge and the read-out identity. -/
theorem spec_of_bridge (input : Input (F circomPrime)) (o : Output (F circomPrime))
    (d : ProverData (F circomPrime)) (hlen : input.len.val ≤ bufferLen)
    (j : Specs.JSON.JSON)
    (hparse : Specs.JSON.parseBytes
      (List.ofFn fun i : Fin input.len.val => bufBytes input.buffer i.val) = some j)
    (htoken : Specs.JSONSchema.IsToken Specs.JSONExtract.google j)
    (hout : outputToNats o = ModelBridge.expected (bufBytes input.buffer) input.len.val)
    (henc : Specs.JSONExtract.encodeOutput (Specs.JSONExtract.GoogleClaims.ofJSON j)
      = ModelBridge.expected (bufBytes input.buffer) input.len.val) :
    Spec input o d := by
  simp only [Spec, dif_pos hlen]
  rw [prefix_toList, hparse]
  exact ⟨htoken, by rw [hout, henc]⟩

end MainSound
end Solution.JSONExtract
