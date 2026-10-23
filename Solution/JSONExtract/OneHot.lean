import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.OneHotTheorems

/-!
# One-hot of a small value (`JSONExtract`)

`OneHot n` witnesses the `n`-wide one-hot indicator of a field element and
pins it: every flag boolean, the flags sum to one, the index-weighted sum
equals the input. Soundness needs no assumption: the rows force the input to
be a value below `n` and the flags to be its indicator.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

namespace OneHot

structure Inputs (F : Type) where
  x : F
deriving ProvableStruct

def main (n : ℕ) [NeZero n] (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var (fields n) (F circomPrime)) := do
  let x := inp.x
  let flags ← Circuit.witnessVector n (.range n fun i => (i =? x.val).toField)
  Circuit.forEach (Vector.finRange n) fun i => assertZero (flags[i] * (flags[i] - 1))
  assertZero ((Fin.foldl n (fun acc i => acc + flags[i]) 0) - 1)
  assertZero (x - Fin.foldl n (fun acc i =>
    acc + flags[i] * (((i.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0)
  return flags

instance elaborated (n : ℕ) [NeZero n] :
    ElaboratedCircuit (F circomPrime) Inputs (fields n) (main n) := by
  elaborate_circuit

/-- The width fits a `u64` (so it is below the field characteristic, else the flag
sum could wrap in soundness, and the witness generator's `u64` index comparison is
exact) and the input is a value the one-hot can represent (else the flag sum row is
unsatisfiable, so completeness fails). Every call site instantiates `n` with a small
numeral, and gets the range bound from the row that produced `x`. -/
def Assumptions (n : ℕ) (inp : Inputs (F circomPrime)) : Prop :=
  n < 2 ^ 64 ∧ inp.x.val < n

/-- The input is below `n` and the flags are its one-hot indicator. -/
def Spec (n : ℕ) (inp : Inputs (F circomPrime)) (flags : fields n (F circomPrime)) : Prop :=
  inp.x.val < n ∧ ∀ i : Fin n, flags[i] = if i.val = inp.x.val then 1 else 0

theorem soundness (n : ℕ) [NeZero n] :
    Soundness (F circomPrime) (main n) (Assumptions n) (Spec n) := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨hn64, -⟩ := h_assumptions
  have hn : n < circomPrime := lt_of_lt_of_le hn64 (by norm_num [circomPrime])
  obtain ⟨h_bool_raw, h_sum_raw, h_wt_raw⟩ := h_holds
  set flags : Vector (F circomPrime) n :=
    Vector.ofFn (fun i : Fin n => env.get (i₀ + i.val)) with hflags
  have hget : ∀ i : Fin n, flags[i.val] = env.get (i₀ + i.val) := by
    intro i; simp [hflags]
  have h_bool : ∀ i : Fin n, IsBool flags[i.val] := by
    intro i
    rw [hget i, IsBool.iff_mul_sub_one]
    exact h_bool_raw i
  have h_sum : (∑ i : Fin n, flags[i.val]) = 1 := by
    rw [LenFlags.eval_foldl_sum] at h_sum_raw
    simp only [Expression.eval, sub_eq_zero] at h_sum_raw
    rw [← h_sum_raw]
    exact Finset.sum_congr rfl (fun i _ => hget i)
  have h_wt : input_x = ∑ i : Fin n, flags[i.val] * ((i.val : ℕ) : F circomPrime) := by
    rw [LenFlags.eval_foldl_sum] at h_wt_raw
    simp only [Expression.eval, sub_eq_zero] at h_wt_raw
    rw [h_wt_raw]
    exact Finset.sum_congr rfl (fun i _ => by rw [hget i])
  obtain ⟨h_lt, h_ind⟩ := onehot_from_constraints hn flags input_x h_bool h_sum h_wt
  exact ⟨h_lt, fun i => by rw [← hget i]; exact h_ind i⟩

theorem completeness (n : ℕ) [NeZero n] :
    Completeness (F circomPrime) (main n) (Assumptions n) := by
  circuit_proof_start [Assumptions]
  obtain ⟨-, h_lt⟩ := h_assumptions
  have hg : ∀ i : Fin n,
      env.get (i₀ + i.val) = if i.val = input_x.val then (1 : F circomPrime) else 0 := by
    intro i; exact h_env i
  refine ⟨fun i => ?_, ?_, ?_⟩
  · rw [hg i]; by_cases h : i.val = input_x.val <;> simp [h]
  · rw [LenFlags.eval_foldl_sum]
    have : (∑ i : Fin n, Expression.eval env.toEnvironment (var { index := i₀ + i.val }))
        = (1 : F circomPrime) := by
      simp only [Expression.eval]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hg i)]
      rw [Finset.sum_eq_single (⟨input_x.val, h_lt⟩ : Fin n)]
      · simp
      · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]; ring
  · rw [LenFlags.eval_foldl_sum]
    have hsum : (∑ i : Fin n, Expression.eval env.toEnvironment
          (var { index := i₀ + i.val } * Expression.const ((i.val : ℕ) : F circomPrime)))
        = ((input_x.val : ℕ) : F circomPrime) := by
      have hstep : ∀ i : Fin n, Expression.eval env.toEnvironment
            (var { index := i₀ + i.val } * Expression.const ((i.val : ℕ) : F circomPrime))
          = (if i.val = input_x.val then (1 : F circomPrime) else 0) * ((i.val : ℕ) : F circomPrime) := by
        intro i; simp only [Expression.eval]; rw [hg i]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i)]
      rw [Finset.sum_eq_single (⟨input_x.val, h_lt⟩ : Fin n)]
      · simp
      · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, ZMod.natCast_val, ZMod.cast_id]
    ring

def circuit (n : ℕ) [NeZero n] : FormalCircuit (F circomPrime) Inputs (fields n) where
  main := main n
  elaborated := elaborated n
  Assumptions := Assumptions n
  Spec := Spec n
  soundness := soundness n
  completeness := completeness n

end OneHot
end Solution.JSONExtract
