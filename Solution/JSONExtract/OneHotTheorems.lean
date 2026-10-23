import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Gadgets.Boolean
import Solution.JSONExtract.LenFlagsTheorems

/-!
# Helper lemmas for the generic `OneHot` gadget

The `LenFlags` one-hot argument, generalized from the fixed `flagLen` width to an
arbitrary width `n` below the field characteristic.  The generic pieces
(`isBool_val`, `natCast_eq_one_of_lt`, `exists_unique_of_sum_eq_one`,
`eval_foldl_sum`) are reused from `LenFlagsTheorems`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

namespace OneHot

/-- A nat sum of `0/1` indicators over `Fin n` whose `F circomPrime`-cast is `1`
is itself `1`, provided the width `n` is below the characteristic. -/
lemma natSum_eq_one_of_cast {n : ℕ} (hn : n < circomPrime) (g : Fin n → ℕ)
    (hb : ∀ i, g i = 0 ∨ g i = 1)
    (h : ((∑ i : Fin n, g i : ℕ) : F circomPrime) = 1) :
    (∑ i : Fin n, g i) = 1 := by
  have h_small : (∑ i : Fin n, g i) < circomPrime := by
    have hle : (∑ i : Fin n, g i) ≤ ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i _; rcases hb i with hi | hi <;> omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hle
    omega
  exact LenFlags.natCast_eq_one_of_lt h_small h

/-- The soundness math, isolated from the circuit context: boolean flags summing
to one, whose index-weighted sum is `msg`, form the one-hot indicator of
`msg.val < n`. -/
lemma onehot_from_constraints {n : ℕ} (hn : n < circomPrime)
    (flags : Vector (F circomPrime) n) (msg : F circomPrime)
    (h_bool : ∀ i : Fin n, IsBool flags[i.val])
    (h_sum : (∑ i : Fin n, flags[i.val]) = 1)
    (h_wt : msg = ∑ i : Fin n, flags[i.val] * ((i.val : ℕ) : F circomPrime)) :
    msg.val < n ∧ ∀ k : Fin n, flags[k] = if k.val = msg.val then 1 else 0 := by
  have hv_bool : ∀ i : Fin n,
      (flags[i.val]).val = 0 ∨ (flags[i.val]).val = 1 :=
    fun i => LenFlags.isBool_val _ (h_bool i)
  have h_cast_sum : ((∑ i : Fin n, (flags[i.val]).val : ℕ) : F circomPrime) = 1 := by
    rw [Nat.cast_sum, ← h_sum]
    apply Finset.sum_congr rfl
    intro i _
    rcases h_bool i with h | h <;>
      simp only [h, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one]
  have h_nat_sum : (∑ i : Fin n, (flags[i.val]).val) = 1 :=
    natSum_eq_one_of_cast hn (fun i => (flags[i.val]).val) hv_bool h_cast_sum
  obtain ⟨ℓ, hℓ_one, hℓ_zero⟩ :=
    LenFlags.exists_unique_of_sum_eq_one (fun i => (flags[i.val]).val) hv_bool h_nat_sum
  have h_indicator : ∀ k : Fin n,
      flags[k] = if k.val = ℓ.val then (1 : F circomPrime) else 0 := by
    intro k
    rcases eq_or_ne k.val ℓ.val with hk | hk
    · have hkeq : k = ℓ := Fin.ext hk
      subst hkeq
      rw [if_pos hk]
      rcases h_bool k with h | h
      · rw [h, ZMod.val_zero] at hℓ_one; exact absurd hℓ_one (by norm_num)
      · exact h
    · have hkne : k ≠ ℓ := fun heq => hk (by rw [heq])
      have hk0 : (flags[k.val]).val = 0 := hℓ_zero k hkne
      rcases h_bool k with h | h
      · rw [if_neg hk]; exact h
      · rw [h, ZMod.val_one] at hk0; exact absurd hk0 (by norm_num)
  have h_term : ∀ i : Fin n,
      flags[i.val] * ((i.val : ℕ) : F circomPrime)
        = (if i.val = ℓ.val then (1 : F circomPrime) else 0) * ((i.val : ℕ) : F circomPrime) := by
    intro i
    have := h_indicator i
    rw [show flags[i.val] = flags[i] from rfl, this]
  have h_msg : msg = ((ℓ.val : ℕ) : F circomPrime) := by
    rw [h_wt, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h_term i)]
    rw [Finset.sum_eq_single ℓ]
    · rw [if_pos rfl, one_mul]
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ ℓ) h
  have hℓ_lt : ℓ.val < n := ℓ.isLt
  have hℓ_lt_p : ℓ.val < circomPrime := lt_trans hℓ_lt hn
  have h_msg_val : msg.val = ℓ.val := by
    rw [h_msg, ZMod.val_natCast_of_lt hℓ_lt_p]
  exact ⟨by rw [h_msg_val]; exact hℓ_lt, fun k => by rw [h_msg_val]; exact h_indicator k⟩

end OneHot
end Solution.JSONExtract
