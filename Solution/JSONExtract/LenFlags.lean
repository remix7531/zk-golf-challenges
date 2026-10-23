import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Gadgets.Boolean
import Solution.JSONExtract.LenFlagsTheorems

/-!
# Length-flag check (`JSONExtract`)

A `FormalAssertion` that the `lenFlags` vector is the one-hot indicator of the
claimed buffer length:
- every flag is boolean,
- the flags sum to one,
- the flag-weighted sum of indices equals `len`.

There are `flagLen = bufferLen + 1` flags, one per buffer position plus the end
position, so a document filling the whole buffer has a flag too. Soundness needs
no assumptions: the constraints force `len.val ≤ bufferLen` and the one-hot
property. This mirrors the SHA-256 `CheckLenFlags` gadget, specialized to the
concrete `circomPrime` and the `bufferLen + 1` flags; the supporting lemmas
are the self-contained copies in `LenFlagsTheorems.lean`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

namespace LenFlags

structure Inputs (F : Type) where
  len : F
  lenFlags : fields flagLen F
deriving ProvableStruct

def main (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  Circuit.forEach (Vector.finRange flagLen) fun i =>
    assertZero (input.lenFlags[i] * (input.lenFlags[i] - 1))
  let flagSum :=
    Fin.foldl flagLen (fun acc i => acc + input.lenFlags[i])
      (0 : Expression (F circomPrime))
  assertZero (flagSum - 1)
  let lenValue :=
    Fin.foldl flagLen
      (fun acc i => acc + input.lenFlags[i] * (((i.val : ℕ) : F circomPrime) : Expression (F circomPrime)))
      (0 : Expression (F circomPrime))
  assertZero (input.len - lenValue)

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

def Spec (input : Inputs (F circomPrime)) : Prop :=
  input.len.val ≤ bufferLen ∧
  OneHotAt input.lenFlags input.len.val

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  -- name the flag values
  set flags := input_lenFlags with hflags
  -- relate evaluated variables to input values
  have h_flag : ∀ i : Fin flagLen,
      Expression.eval env input_var_lenFlags[i.val] = flags[i.val] := by
    intro i
    have := Vector.ext_iff.mp h_input.2 i.val i.isLt
    simpa [Vector.getElem_map] using this
  obtain ⟨h_bool_raw, h_sum_raw, h_wt_raw⟩ := h_holds
  -- booleanity of each flag
  have h_bool : ∀ i : Fin flagLen, IsBool flags[i.val] := by
    intro i
    have := h_bool_raw i
    rw [h_flag i] at this
    rw [IsBool.iff_mul_sub_one]
    exact this
  -- the field sum of flags equals 1
  have h_sum : (∑ i : Fin flagLen, flags[i.val]) = 1 := by
    rw [eval_foldl_sum] at h_sum_raw
    have : (∑ i : Fin flagLen, Expression.eval env input_var_lenFlags[i.val]) = 1 := by
      have := h_sum_raw
      simp only [sub_eq_zero] at this
      exact this
    rw [← this]
    apply Finset.sum_congr rfl
    intro i _
    exact (h_flag i).symm
  -- the weighted sum equals len
  have h_wt : input_len = ∑ i : Fin flagLen, flags[i.val] * ((i.val : ℕ) : F circomPrime) := by
    rw [eval_foldl_sum] at h_wt_raw
    have heq : (∑ i : Fin flagLen,
        Expression.eval env (input_var_lenFlags[i.val] * Expression.const ((i.val : ℕ) : F circomPrime)))
        = ∑ i : Fin flagLen, flags[i.val] * ((i.val : ℕ) : F circomPrime) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Expression.eval]
      rw [h_flag i]
    rw [heq] at h_wt_raw
    rw [sub_eq_zero] at h_wt_raw
    exact h_wt_raw
  obtain ⟨h_lt, h_onehot⟩ := onehot_from_constraints flags input_len h_bool h_sum h_wt
  exact ⟨Nat.le_of_lt_succ h_lt, h_onehot⟩

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_len_le, h_onehot⟩ := h_spec
  have h_len_lt : input_len.val < flagLen := Nat.lt_succ_of_le h_len_le
  -- relate evaluated variables to input values
  have h_flag : ∀ i : Fin flagLen,
      Expression.eval env input_var_lenFlags[i.val] = input_lenFlags[i.val] := by
    intro i
    have := Vector.ext_iff.mp h_input.2 i.val i.isLt
    simpa [Vector.getElem_map] using this
  -- one-hot value of each flag
  have h_flag_val : ∀ k : Fin flagLen,
      Expression.eval env input_var_lenFlags[k.val] =
        if k.val = input_len.val then 1 else 0 := by
    intro k
    rw [h_flag k]
    exact h_onehot k
  refine ⟨?_, ?_, ?_⟩
  · -- booleanity
    intro i
    rw [h_flag_val i]
    by_cases h : i.val = input_len.val <;> simp [h]
  · -- flags sum to 1
    rw [eval_foldl_sum]
    have : (∑ i : Fin flagLen, Expression.eval env.toEnvironment input_var_lenFlags[i.val]) = 1 := by
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h_flag_val i)]
      rw [Finset.sum_eq_single (⟨input_len.val, h_len_lt⟩ : Fin flagLen)]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (Fin.ext h))]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]; ring
  · -- weighted sum equals len
    rw [eval_foldl_sum]
    have hsum : (∑ i : Fin flagLen,
        Expression.eval env (input_var_lenFlags[i.val] * Expression.const ((i.val : ℕ) : F circomPrime)))
        = ((input_len.val : ℕ) : F circomPrime) := by
      have hstep : ∀ i : Fin flagLen,
          Expression.eval env.toEnvironment (input_var_lenFlags[i.val] * Expression.const ((i.val : ℕ) : F circomPrime))
          = (if i.val = input_len.val then 1 else 0) * ((i.val : ℕ) : F circomPrime) := by
        intro i
        simp only [Expression.eval]
        rw [h_flag_val i]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i)]
      rw [Finset.sum_eq_single ⟨input_len.val, h_len_lt⟩]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (Fin.ext h))]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum]
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring

def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end LenFlags
end Solution.JSONExtract
