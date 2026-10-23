import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.LenFlagsTheorems

/-!
# Filled-cell mask of an output slot (`JSONExtract`)

`FilledMask n` pins a slot of `n` cells against its length: a witnessed mask
that is boolean, monotone (once a cell is unfilled, every later one is), and
sums to the length, and every cell is masked to `0` where the mask is off. So
the mask is exactly `[t < len]` and every padding cell is zero.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

namespace FilledMask

structure Inputs (n : ℕ) (F : Type) where
  cells : Vector F n
  len : F
deriving ProvableStruct

def main (n : ℕ) [NeZero n] (inp : Var (Inputs n) (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let filled ← Circuit.witnessVector n (.range n fun t => (t <? inp.len.val).toField)
  Circuit.forEach (Vector.finRange n) fun t =>
    assertZero (filled[t] * (filled[t] - 1))
  Circuit.forEach (Vector.finRange n) fun t =>
    assertZero (filled[t] * (1 - filled[t.val - 1]'(by have := t.isLt; omega)))
  assertZero ((Fin.foldl n (fun acc t => acc + filled[t]) 0) - inp.len)
  Circuit.forEach (Vector.finRange n) fun t =>
    assertZero (inp.cells[t] * (1 - filled[t]))

instance elaborated (n : ℕ) [NeZero n] :
    ElaboratedCircuit (F circomPrime) (Inputs n) unit (main n) := by
  elaborate_circuit

/-- The slot width fits a `u64` (so the witness generator's `u64` comparison of the
index against the length is exact, and the flag sum cannot wrap in soundness). Every
call site instantiates `n` with a small numeral.

The length bound `inp.len.val ≤ n` is deliberately *not* assumed: it is forced by the
sum row (the flags are boolean, so their sum is at most `n`), and `Main.soundness`
-- where a cheating prover picks the slot length -- could never discharge it. -/
def Assumptions (n : ℕ) (_inp : Inputs n (F circomPrime)) : Prop :=
  n < 2 ^ 64

/-- The length fits the slot and every cell at or past it is zero. -/
def Spec (n : ℕ) (inp : Inputs n (F circomPrime)) : Prop :=
  inp.len.val ≤ n ∧ ∀ t : Fin n, inp.len.val ≤ t.val → inp.cells[t] = 0

/-- `∑_{i < n} [i < k] = k` in the field, for a threshold `k` inside the range. -/
lemma sum_indicator_lt (n k : ℕ) (hk : k ≤ n) :
    ∑ i : Fin n, (if i.val < k then (1 : F circomPrime) else 0) = (k : F circomPrime) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then (1 : F circomPrime) else 0) n,
    Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) hk]
  have h1 : ∑ i ∈ Finset.Ico 0 k, (if i < k then (1 : F circomPrime) else 0)
      = (k : F circomPrime) := by
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_Ico.mp hi).2)]
    simp
  have h2 : ∑ i ∈ Finset.Ico k n, (if i < k then (1 : F circomPrime) else 0) = 0 := by
    rw [Finset.sum_congr rfl (fun i hi => if_neg (Nat.not_lt.mpr (Finset.mem_Ico.mp hi).1))]
    simp
  rw [h1, h2, add_zero]

/-- The soundness math, isolated from the circuit context: a boolean mask that is
monotone (a set cell forces its predecessor set) and whose entries sum to `len` is off
at every cell at or past `len`. Counting: the set cells are downward closed, so a set
cell at `t` forces `t + 1` set cells, while the total number of set cells is `len.val`. -/
lemma mask_off_past_len {n : ℕ} (hn : n < circomPrime) (f : Fin n → F circomPrime)
    (len : F circomPrime)
    (h_bool : ∀ t : Fin n, IsBool (f t))
    (h_step : ∀ (t : Fin n) (h : t.val - 1 < n), f t = 1 → f ⟨t.val - 1, h⟩ = 1)
    (h_sum : ∑ t : Fin n, f t = len) :
    len.val ≤ n ∧ ∀ t : Fin n, len.val ≤ t.val → f t = 0 := by
  -- one step of monotonicity iterates to full downward closure
  have h_down : ∀ (d : ℕ) (t : Fin n) (h : t.val - d < n), f t = 1 → f ⟨t.val - d, h⟩ = 1 := by
    intro d
    induction d with
    | zero => intro t h ht; simpa using ht
    | succ d ih =>
      intro t h ht
      have h' : t.val - d < n := by omega
      have h2 : (⟨t.val - d, h'⟩ : Fin n).val - 1 < n := by omega
      have h3 := h_step ⟨t.val - d, h'⟩ h2 (ih t h' ht)
      have he : (⟨(⟨t.val - d, h'⟩ : Fin n).val - 1, h2⟩ : Fin n) = ⟨t.val - (d + 1), h⟩ :=
        -- `simp only []` reduces the `Fin.val` of the anonymous constructors for `omega`
        Fin.ext (by simp only []; omega)
      rwa [he] at h3
  have h_closed : ∀ s t : Fin n, s.val ≤ t.val → f t = 1 → f s = 1 := by
    intro s t hst ht
    have h : t.val - (t.val - s.val) < n := by omega
    have h1 := h_down (t.val - s.val) t h ht
    have he : (⟨t.val - (t.val - s.val), h⟩ : Fin n) = s := Fin.ext (by simp only []; omega)
    rwa [he] at h1
  -- the number of set cells is `len.val`
  have hv : ∀ t : Fin n, (f t).val = 0 ∨ (f t).val = 1 := fun t => LenFlags.isBool_val _ (h_bool t)
  have h_nat_le : (∑ t : Fin n, (f t).val) ≤ n := by
    have hle : (∑ t : Fin n, (f t).val) ≤ ∑ _t : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro t _; rcases hv t with h | h <;> omega
    simpa using hle
  have h_cast : ((∑ t : Fin n, (f t).val : ℕ) : F circomPrime) = len := by
    rw [Nat.cast_sum, ← h_sum]
    exact Finset.sum_congr rfl fun t _ => by
      rcases h_bool t with h | h <;> simp [h]
  have h_len_val : len.val = ∑ t : Fin n, (f t).val := by
    rw [← h_cast, ZMod.val_natCast_of_lt (lt_of_le_of_lt h_nat_le hn)]
  refine ⟨by omega, ?_⟩
  -- a set cell sits strictly below the number of set cells
  intro t hle
  rcases h_bool t with h | h
  · exact h
  · exfalso
    have hIic : ∑ s ∈ Finset.Iic t, (f s).val = t.val + 1 := by
      have hone : ∀ s ∈ Finset.Iic t, (f s).val = 1 := by
        intro s hs
        rw [h_closed s t (Fin.le_def.mp (Finset.mem_Iic.mp hs)) h, ZMod.val_one]
      rw [Finset.sum_congr rfl hone, Finset.sum_const, Fin.card_Iic, smul_eq_mul, mul_one]
    have hsub : ∑ s ∈ Finset.Iic t, (f s).val ≤ ∑ s : Fin n, (f s).val :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega

theorem soundness (n : ℕ) [NeZero n] :
    FormalAssertion.Soundness (F circomPrime) (main n) (Assumptions n) (Spec n) := by
  circuit_proof_start [Assumptions, Spec]
  have hn64 := h_assumptions
  have hn : n < circomPrime := lt_of_lt_of_le hn64 (by norm_num [circomPrime])
  obtain ⟨h_bool_raw, h_mono_raw, h_sum_raw, h_cells_raw⟩ := h_holds
  have h_bool : ∀ s : Fin n, IsBool (env.get (i₀ + s.val)) := by
    intro s; rw [IsBool.iff_mul_sub_one]; exact h_bool_raw s
  have h_step : ∀ (s : Fin n) (h : s.val - 1 < n),
      env.get (i₀ + s.val) = 1 → env.get (i₀ + (⟨s.val - 1, h⟩ : Fin n).val) = 1 := by
    intro s h hs
    have h1 := h_mono_raw s
    rw [hs, one_mul, sub_eq_zero] at h1
    exact h1.symm
  have h_sum : ∑ s : Fin n, env.get (i₀ + s.val) = input_len := by
    rw [LenFlags.eval_foldl_sum] at h_sum_raw
    simp only [Expression.eval, sub_eq_zero] at h_sum_raw
    exact h_sum_raw
  obtain ⟨hfit, hoff⟩ := mask_off_past_len hn (fun s : Fin n => env.get (i₀ + s.val))
    input_len h_bool h_step h_sum
  refine ⟨hfit, fun t ht => ?_⟩
  have hzero := hoff t ht
  have hcell : Expression.eval env input_var_cells[t.val] = input_cells[t.val] := by
    have := Vector.ext_iff.mp h_input.1 t.val t.isLt
    simpa [Vector.getElem_map] using this
  have hc := h_cells_raw t
  rw [hcell, hzero, sub_zero, mul_one] at hc
  exact hc

theorem completeness (n : ℕ) [NeZero n] :
    FormalAssertion.Completeness (F circomPrime) (main n) (Assumptions n) (Spec n) := by
  circuit_proof_start [Assumptions, Spec]
  have hlen : input_len.val ≤ n := h_spec.1
  obtain ⟨hg, -, -⟩ := h_env
  have hcell : ∀ i : Fin n,
      Expression.eval env.toEnvironment input_var_cells[i.val] = input_cells[i.val] := by
    intro i
    have := Vector.ext_iff.mp h_input.1 i.val i.isLt
    simpa [Vector.getElem_map] using this
  refine ⟨fun i => ?_, fun i => ?_, ?_, fun i => ?_⟩
  · rw [hg i]; by_cases h : i.val < input_len.val <;> simp [h]
  · have h' : i.val - 1 < n := by omega
    have e2 : env.get (i₀ + (i.val - 1)) = if i.val - 1 < input_len.val then 1 else 0 :=
      hg ⟨i.val - 1, h'⟩
    rw [hg i, e2]
    by_cases h : i.val < input_len.val
    · have h2 : i.val - 1 < input_len.val := by omega
      simp [h, h2]
    · simp [h]
  · rw [LenFlags.eval_foldl_sum]
    have hterm : ∀ i : Fin n,
        Expression.eval env.toEnvironment (var { index := i₀ + i.val } : Expression (F circomPrime))
          = if i.val < input_len.val then (1 : F circomPrime) else 0 := fun i => hg i
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
      sum_indicator_lt n input_len.val hlen, ZMod.natCast_val, ZMod.cast_id, sub_self]
  · rw [hg i, hcell i]
    by_cases h : i.val < input_len.val
    · simp [h]
    · rw [h_spec.2 i (by omega)]
      simp

def circuit (n : ℕ) [NeZero n] : FormalAssertion (F circomPrime) (Inputs n) := {
  main := main n, elaborated := elaborated n, Assumptions := Assumptions n, Spec := Spec n
  soundness := soundness n
  completeness := completeness n
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end FilledMask
end Solution.JSONExtract
