import Solution.JSONExtract.MainSoundness

/-!
# The honest prover's view of `main` (`JSONExtract`)

`Main.completeness` peels `main`'s spine the other way round: each block is
*constructed*, and the witness-IR sites hand the continuation the fact that the
variables they bind evaluate to the run's projections (`Witgen.lean`'s eleven
bridges).  What is left is to read those projections back as the model
registers, which is what this file does, and to discharge each gadget's
`ProverAssumptions` / `Assumptions` + `Spec`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSt nSub nClaims kIdxMax ofsMax St Sub Claim Regs)
open Witness (slots)

namespace MainComplete

open Model (run step runSignals signals)
open MainSound

/-! ## Reading a witnessed block back -/

theorem toElements_fields {m : ℕ} (v : Vector (Expression (F circomPrime)) m) :
    ProvableType.toElements (M := fields m) v = v := rfl

/-- A block whose elements evaluate to those of `x` evaluates to `x`. -/
theorem eval_of_toElements {M : TypeMap} [ProvableType M] (env : Environment (F circomPrime))
    (v : Var M (F circomPrime)) (x : M (F circomPrime))
    (h : ∀ (i : ℕ) (hi : i < size M),
      Expression.eval env ((ProvableType.toElements (M := M) v)[i]'hi)
        = (ProvableType.toElements (M := M) x)[i]'hi) :
    (eval env v : M (F circomPrime)) = x := by
  have hv : ProvableType.toElements (eval env v : M (F circomPrime))
      = ProvableType.toElements x := by
    apply Vector.ext
    intro i hi
    rw [← ProvableType.getElem_eval_toElements]
    exact h i hi
  calc (eval env v : M (F circomPrime))
      = ProvableType.fromElements (ProvableType.toElements (eval env v : M _)) :=
        (ProvableType.fromElements_toElements _).symm
    _ = ProvableType.fromElements (ProvableType.toElements x) := by rw [hv]
    _ = x := ProvableType.fromElements_toElements _

/-- `witnessVector` wraps its output into a step-free IR program; `lenFlagsIR` is
sealed, so the identification needs its equation. -/
theorem lenFlagsIR_def (input : Var Input (F circomPrime)) :
    IR.lenFlagsIR input = Witgen.WitgenIR.ir [] (IR.lenFlagsOut input) := by
  unfold IR.lenFlagsIR
  rfl

theorem accmIR_def (input : Var Input (F circomPrime)) :
    IR.accmIR input = Witgen.WitgenIR.ir [] (IR.accmOut input) := by
  unfold IR.accmIR
  rfl

/-! ## The run's projections, read at a position -/

theorem div_mod_slot {n : ℕ} (hn : 0 < n) (i : ℕ) (j : Fin n) :
    (i * n + j.val) / n = i ∧ (i * n + j.val) % n = j.val := by
  have e : i * n + j.val = j.val + n * i := by ring
  refine ⟨?_, ?_⟩
  · rw [e, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]

theorem ind_eq_ite {P : Prop} [Decidable P] (b : Bool) (h : b = true ↔ P) :
    Witness.ind b = if P then (1 : F circomPrime) else 0 := by
  by_cases hp : P
  · rw [if_pos hp, Witness.ind, if_pos (h.mpr hp)]
  · rw [if_neg hp, Witness.ind, if_neg (fun hb => hp (h.mp hb))]

theorem stGen_get (bytes : ℕ → ℕ) (len i : ℕ) (j : Fin nSt) (h : i * nSt + j.val < nSt * slots) :
    (Witness.stGen bytes len)[i * nSt + j.val]'h
      = if j = (run bytes len i).st then 1 else 0 := by
  obtain ⟨hd, hm⟩ := div_mod_slot (n := nSt) (by decide) i j
  rw [Witness.stGen, Vector.getElem_ofFn]
  simp only [hd, hm]
  exact ind_eq_ite _ (by simp [Fin.ext_iff, eq_comm])

theorem subGen_get (bytes : ℕ → ℕ) (len i : ℕ) (j : Fin nSub)
    (h : i * nSub + j.val < nSub * slots) :
    (Witness.subGen bytes len)[i * nSub + j.val]'h
      = if j = (run bytes len i).sub then 1 else 0 := by
  obtain ⟨hd, hm⟩ := div_mod_slot (n := nSub) (by decide) i j
  rw [Witness.subGen, Vector.getElem_ofFn]
  simp only [hd, hm]
  exact ind_eq_ite _ (by simp [Fin.ext_iff, eq_comm])

theorem mGen_get (bytes : ℕ → ℕ) (len i : ℕ) (k : Claim)
    (h : i * nClaims + k.val < nClaims * slots) :
    (Witness.mGen bytes len)[i * nClaims + k.val]'h
      = if (run bytes len i).m[k] then 1 else 0 := by
  obtain ⟨hd, hm⟩ := div_mod_slot (n := nClaims) (by decide) i k
  rw [Witness.mGen, Vector.getElem_ofFn]
  simp only [hd, hm, Fin.getElem_fin]
  exact ind_eq_ite _ Iff.rfl

theorem claimGen_get (bytes : ℕ → ℕ) (len i : ℕ) (k : Claim)
    (h : i * nClaims + k.val < nClaims * slots) :
    (Witness.claimGen bytes len)[i * nClaims + k.val]'h
      = if (run bytes len i).claim = some k then 1 else 0 := by
  obtain ⟨hd, hm⟩ := div_mod_slot (n := nClaims) (by decide) i k
  rw [Witness.claimGen, Vector.getElem_ofFn]
  simp only [hd, hm]
  exact ind_eq_ite _ (by simp [Fin.eta])

/-! ## The routed cells of the honest output -/

theorem cellsGen_get (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) (n t : ℕ) (ht : t < n) :
    (Witness.cellsGen bytes len k n)[t]?.getD 0
      = ((Model.cell bytes len k t : ℕ) : F circomPrime) := by
  rw [MainSound.gd _ _ ht, Witness.cellsGen, Vector.getElem_ofFn]

set_option maxHeartbeats 1000000 in
theorem outCell_outputGen (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) (t : ℕ)
    (ht : t < Model.claimCap k) :
    Step.outCell (Witness.outputGen bytes len) k t
      = ((Model.cell bytes len k t : ℕ) : F circomPrime) := by
  fin_cases k <;>
    simp only [Step.outCell, Witness.outputGen, Witness.strSlotGen, Witness.intSlotGen,
      Witness.boolSlotGen] <;>
    first
      | exact cellsGen_get bytes len _ _ t ht
      | exact absurd ht (Nat.not_lt_zero t)

/-- The parse the honest prover's assumptions promise. -/
theorem token_of_prover (input : Input (F circomPrime)) (hlen : input.len.val ≤ bufferLen)
    (h : if h : input.len.val ≤ bufferLen then
          match Specs.JSON.parseBytes (Specs.JSONExtract.takePrefix
            (fieldElemsToNat input.buffer) input.len.val h).toList with
          | some j => Specs.JSONSchema.IsToken Specs.JSONExtract.google j
          | none => False
        else False) :
    ∃ j, Specs.JSON.parseBytes
        (List.ofFn fun i : Fin input.len.val => MainSound.bufBytes input.buffer i.val) = some j
      ∧ Specs.JSONSchema.IsToken Specs.JSONExtract.google j := by
  rw [dif_pos hlen, MainSound.prefix_toList] at h
  cases hp : Specs.JSON.parseBytes
      (List.ofFn fun i : Fin input.len.val => MainSound.bufBytes input.buffer i.val) with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some j => exact ⟨j, rfl, by rw [hp] at h; exact h⟩

/-- A slice of a position-major register, read at one state. -/
theorem slice_get (env : Environment (F circomPrime)) {n : ℕ} (v : Vector E (n * slots))
    (i : ℕ) (hi : i < slots) (j : Fin n) :
    (eval env (sliceAt n v i hi) : Vector (F circomPrime) n)[j.val]
      = Expression.eval env (v[i * n + j.val]?.getD 0) := by
  rw [MainSound.eval_sliceAt, Vector.getElem_ofFn]

/-! ## The honest `Rows` -/

section Honest

variable {R : RunVals} {bytes : ℕ → ℕ} {len : ℕ} {d : ProverData (F circomPrime)}

theorem accm_row (len i : ℕ) :
    (if len < i + 1 then (1 : F circomPrime) else 0)
      = (if len < i then 1 else 0) + (if i = len then 1 else 0) := by
  by_cases h1 : len < i
  · rw [if_pos h1, if_pos (by omega), if_neg (by omega)]; ring
  · rw [if_neg h1]
    by_cases h2 : i = len
    · rw [if_pos h2, if_pos (by omega)]; ring
    · rw [if_neg h2, if_neg (by omega)]; ring

theorem rows_of_honest (hbyteVal : ∀ i, i < bufferLen → (R.byteF i).val = bytes i)
    (hbyteLt : ∀ i, bytes i < 256) (hlenLe : len ≤ bufferLen)
    (hlenFlag : ∀ i, i < bufferLen → R.lenFlagF i = if i = len then 1 else 0)
    (haccm : ∀ i, i < slots → R.accmF i = if len < i then 1 else 0)
    (henc : ∀ i, i < slots → Enc R i (run bytes len i))
    (hstepSpec : ∀ i : Fin bufferLen,
      Step.Assumptions (R.row i.val) d → Step.Spec (R.row i.val) (R.sigF i.val) d)
    (hacc : Model.accepts bytes len = true) :
    Rows R bytes len d := by
  obtain ⟨hsteps, hend, hsubP, hmem, hpres⟩ := (ModelBridge.accepts_iff bytes len).mp hacc
  have h0 : (0 : ℕ) < slots := by simp only [Witness.slots]; omega
  have hB : bufferLen < slots := by simp only [Witness.slots]; omega
  have hfr : run bytes len bufferLen = run bytes len len :=
    RunTheory.run_frozen bytes len bufferLen hlenLe
  refine ⟨hbyteVal, hbyteLt, hlenLe, hlenFlag, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hstepSpec,
    ?_, ?_, ?_⟩
  · rw [haccm 0 h0, if_neg (by omega)]
  · rw [(henc 0 h0).1 St.PRE, if_pos (show St.PRE = (run bytes len 0).st from rfl)]
  · rw [(henc 0 h0).2.1 Sub.PLAIN, if_pos (show Sub.PLAIN = (run bytes len 0).sub from rfl)]
  · rw [(henc 0 h0).2.2.1, show (run bytes len 0).hexAcc = 0 from rfl, Nat.cast_zero]
  · rw [(henc 0 h0).2.2.2.1, show (run bytes len 0).kIdx = 0 from rfl, Nat.cast_zero]
  · rw [(henc 0 h0).2.2.2.2.2.2.1, show (run bytes len 0).ofs = 0 from rfl, Nat.cast_zero]
  · rw [(henc 0 h0).2.2.2.2.2.2.2, show (run bytes len 0).nMem = 0 from rfl, Nat.cast_zero]
  · intro k
    rw [(henc 0 h0).2.2.2.2.1 k]
    exact if_neg (show ¬ (Model.Regs.init.m[k] = true) by simp [Model.Regs.init])
  · intro k
    rw [(henc 0 h0).2.2.2.2.2.1 k]
    exact if_neg (show ¬ (Model.Regs.init.claim = some k) by simp [Model.Regs.init])
  · rw [(henc bufferLen hB).1 St.END, if_pos (by rw [hfr]; exact hend.symm)]
  · rw [(henc bufferLen hB).2.1 Sub.PLAIN, if_pos (by rw [hfr]; exact hsubP.symm)]
  · rw [(henc bufferLen hB).2.2.2.2.2.2.2]
    have hnm := IR.run_nMem_le bytes len bufferLen
    have hp : (bufferLen : ℕ) < circomPrime := by decide
    rw [MainSound.val_cast_lt (show (run bytes len bufferLen).nMem < circomPrime by omega), hfr]
    exact hmem

set_option maxHeartbeats 1000000 in
/-- The honest prover's view of one position. -/
theorem step_proverAssumptions
    (hbyteVal : ∀ i, i < bufferLen → (R.byteF i).val = bytes i)
    (hbyteLt : ∀ i, bytes i < 256) (hlenLe : len ≤ bufferLen)
    (hlenFlag : ∀ i, i < bufferLen → R.lenFlagF i = if i = len then 1 else 0)
    (haccm : ∀ i, i < slots → R.accmF i = if len < i then 1 else 0)
    (henc : ∀ i, i < slots → Enc R i (run bytes len i))
    (hout : R.outV = Witness.outputGen bytes len)
    (hacc : Model.accepts bytes len = true)
    (i : ℕ) (hi : i < bufferLen) (hint : ProverHint (F circomPrime)) :
    Step.ProverAssumptions (R.row i) d hint := by
  obtain ⟨hsteps, hend, hsubP, hmem, hpres⟩ := (ModelBridge.accepts_iff bytes len).mp hacc
  have hs1 : i < slots := by simp only [Witness.slots]; omega
  have hs2 : i + 1 < slots := by simp only [Witness.slots]; omega
  have hbv : (R.row i).byte.val = bytes i := hbyteVal i hi
  simp only [Step.ProverAssumptions]
  rw [hbv]
  refine ⟨hbyteLt i, run bytes len i, RunTheory.run_wf bytes len i,
    (encodesPrev_iff R i _).mpr (henc i hs1), ?_, ?_⟩
  · show R.accmF (i + 1) = R.accmF i + R.lenFlagF i
    rw [haccm (i + 1) hs2, haccm i hs1, hlenFlag i hi]
    exact accm_row len i
  · by_cases hact : i < len
    · right
      refine ⟨?_, ?_⟩
      · show R.accmF (i + 1) = 0
        rw [haccm (i + 1) hs2, if_neg (by omega)]
      · obtain ⟨r', hstep'⟩ := Option.isSome_iff_exists.mp (hsteps i hact)
        have hrun : run bytes len (i + 1) = r' := RunTheory.run_succ_of_step hact hstep'
        refine ⟨r', hstep', (encodesNext_iff R i r').mpr (hrun ▸ henc (i + 1) hs2), ?_⟩
        intro k hw hcl
        have hsg : runSignals bytes len i = signals (run bytes len i) (bytes i) r'.st :=
          RunTheory.runSignals_pos bytes len hact hstep'
        have hk : Model.kindOf (run bytes len i).claim = Model.Kind.str
            ∨ Model.kindOf (run bytes len i).claim = Model.Kind.int := by
          have hw' := hw
          rw [Step.sig_write] at hw'
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw'
          exact hw'.2
        rw [hcl] at hk
        have hkind := RunTheory.isStr_or_isInt_of_kind k hk
        have hcap : (run bytes len i).ofs < Model.claimCap k := Step.step_capOk hstep' hw k hcl
        have hei : RunTheory.emitsAt bytes len k i = true := by
          simp only [RunTheory.emitsAt, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨?_, hcl⟩
          rw [hsg, ← RunTheory.write_eq_vEmit_sig k hkind hcl]
          exact hw
        rw [row_out, hout, outCell_outputGen bytes len k _ hcap,
          RunTheory.cell_eq_valOut bytes len k hkind hsteps (hpres k) hact hei, hsg]
    · left
      refine ⟨?_, ?_, ?_⟩
      · show R.accmF (i + 1) = 1
        rw [haccm (i + 1) hs2, if_pos (by omega)]
      · refine (encodesNext_iff R i _).mpr ?_
        have hfrz : run bytes len (i + 1) = run bytes len i := by
          rw [RunTheory.run_succ, if_neg hact]
        rw [← hfrz]
        exact henc (i + 1) hs2
      · have hrun : run bytes len i = run bytes len len :=
          RunTheory.run_frozen bytes len i (by omega)
        have hst : (run bytes len i).st = St.END := by rw [hrun]; exact hend
        exact (RunTheory.signals_end (run bytes len i) (bytes i) hst).2.2.1

/-! ## The end pins on the honest output -/

theorem count_lt (hlenLe : len ≤ bufferLen) {m : ℕ} (h : m ≤ len) : m < circomPrime := by
  have h2 : (bufferLen : ℕ) < circomPrime := by decide
  omega

theorem isBool_presentCount (hlenLe : len ≤ bufferLen) {k : Claim}
    (hpres : Model.presentCount bytes len k ≤ 1) :
    IsBool (((Model.presentCount bytes len k : ℕ) : F circomPrime)) := by
  rcases Nat.lt_or_ge (Model.presentCount bytes len k) 1 with h | h
  · left; rw [show Model.presentCount bytes len k = 0 by omega]; simp
  · right; rw [show Model.presentCount bytes len k = 1 by omega]; simp

theorem strSlotPin_honest (k : Claim) (n : ℕ) (hn : Model.claimCap k = n)
    (hkind : Model.isStrClaim k = true ∨ Model.isIntClaim k = true) (hlenLe : len ≤ bufferLen)
    (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
    (hpres : Model.presentCount bytes len k ≤ 1) :
    StrSlotPin.Spec n ⟨Witness.strSlotGen bytes len k n,
      ((Model.presentCount bytes len k : ℕ) : F circomPrime),
      ((Model.slotLen bytes len k : ℕ) : F circomPrime)⟩ := by
  have hcap := RunTheory.slotLen_le_claimCap bytes len k hkind hsteps hpres
  have hvl : (((Model.slotLen bytes len k : ℕ) : F circomPrime)).val
      = Model.slotLen bytes len k :=
    MainSound.val_cast_lt (count_lt hlenLe (RunTheory.slotLen_le bytes len k))
  refine ⟨isBool_presentCount hlenLe hpres, rfl, rfl, ?_, ?_⟩
  · rw [hvl]; omega
  · intro t htge
    rw [hvl] at htge
    show (Witness.cellsGen bytes len k n)[t.val] = 0
    rw [Witness.cellsGen, Vector.getElem_ofFn,
      RunTheory.cell_eq_zero bytes len k hkind hsteps hpres htge]
    simp

theorem intSlotPin_honest (k : Claim) (n : ℕ) (hn : Model.claimCap k = n)
    (hkind : Model.isStrClaim k = true ∨ Model.isIntClaim k = true) (hlenLe : len ≤ bufferLen)
    (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
    (hpres : Model.presentCount bytes len k ≤ 1) :
    IntSlotPin.Spec n ⟨Witness.intSlotGen bytes len k n,
      ((Model.presentCount bytes len k : ℕ) : F circomPrime),
      ((Model.signCount bytes len k : ℕ) : F circomPrime),
      ((Model.slotLen bytes len k : ℕ) : F circomPrime)⟩ := by
  have hcap := RunTheory.slotLen_le_claimCap bytes len k hkind hsteps hpres
  have hvl : (((Model.slotLen bytes len k : ℕ) : F circomPrime)).val
      = Model.slotLen bytes len k :=
    MainSound.val_cast_lt (count_lt hlenLe (RunTheory.slotLen_le bytes len k))
  refine ⟨isBool_presentCount hlenLe hpres, rfl, rfl, rfl, ?_, ?_⟩
  · rw [hvl]; omega
  · intro t htge
    rw [hvl] at htge
    show (Witness.cellsGen bytes len k n)[t.val] = 0
    rw [Witness.cellsGen, Vector.getElem_ofFn,
      RunTheory.cell_eq_zero bytes len k hkind hsteps hpres htge]
    simp

theorem boolSlotPin_honest (hlenLe : len ≤ bufferLen)
    (hpres : Model.presentCount bytes len 6 ≤ 1) :
    BoolSlotPin.Spec ⟨Witness.boolSlotGen bytes len 6,
      ((Model.presentCount bytes len 6 : ℕ) : F circomPrime),
      ((Model.trueCount bytes len 6 : ℕ) : F circomPrime)⟩ :=
  ⟨isBool_presentCount hlenLe hpres, rfl, rfl⟩

end Honest

end MainComplete
end Solution.JSONExtract
