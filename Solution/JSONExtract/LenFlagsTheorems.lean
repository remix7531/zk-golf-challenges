import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Gadgets.Boolean

/-!
# Helper lemmas for the `JSONExtract` `LenFlags` one-hot gadget

This file is self-contained (per `LEAN_STYLE.md`, solutions may not import files
from other solutions): the definitions and lemmas here are adapted from the
SHA-256 `CheckLenFlags` gadget (`Solution/SHA256/Common.lean` and
`Solution/SHA256/CheckLenFlagsTheorems.lean`), specialized to the concrete
`circomPrime` and the `bufferLen + 1` length flags.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

/-- Number of length flags: one per buffer position plus the end position
`bufferLen`, so every length `len ≤ bufferLen` has a slot (matches
`Witness.slots`). -/
@[reducible] def flagLen : ℕ := bufferLen + 1

/-- The largeness fact the soundness argument needs (`CheckLenFlags` asks for
`Fact (p > 2^33)`; `circomPrime ≈ 2^254` so this holds). -/
instance factCircomGt2_33 : Fact (circomPrime > 2 ^ 33) :=
  ⟨by unfold circomPrime; norm_num⟩

instance : Fact (circomPrime > 2) :=
  .mk (by
    have h : (2 : ℕ) < 2 ^ 33 := by norm_num
    exact h.trans factCircomGt2_33.out)

/-- `flags` is the one-hot indicator vector of the value `ℓ`. -/
def OneHotAt (flags : Vector (F circomPrime) flagLen) (ℓ : ℕ) : Prop :=
  ∀ k : Fin flagLen, flags[k] = if k.val = ℓ then 1 else 0

namespace LenFlags

/-- `Expression.eval` distributes over a `Fin.foldl` summation. -/
lemma eval_foldl_sum {n : ℕ} (env : Environment (F circomPrime))
    (g : Fin n → Expression (F circomPrime)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0) =
      ∑ i : Fin n, Expression.eval env (g i) := by
  induction n with
  | zero => simp only [Fin.foldl_zero, Finset.univ_eq_empty, Finset.sum_empty]; rfl
  | succ m ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    simp only [Expression.eval]
    rw [show (Fin.foldl m (fun (x1 : Expression (F circomPrime)) (x2 : Fin m) =>
        x1 + g x2.castSucc) 0) =
        Fin.foldl m (fun acc i => acc + (g ∘ Fin.castSucc) i) 0 from rfl]
    rw [ih (g ∘ Fin.castSucc)]
    rfl

/-- A boolean field element equals the cast of its `val`, which is `0` or `1`. -/
lemma isBool_val (x : F circomPrime) (h : IsBool x) : x.val = 0 ∨ x.val = 1 := by
  rcases h with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]

/-- If a small nat casts to `1` in `F circomPrime`, it is `1`. -/
lemma natCast_eq_one_of_lt {m : ℕ} (hm : m < circomPrime)
    (h : ((m : ℕ) : F circomPrime) = 1) : m = 1 := by
  have hval := ZMod.val_natCast_of_lt hm
  rw [h, ZMod.val_one] at hval
  exact hval.symm

/-- If a nat sum of `0/1` indicators over `Fin n` equals `1`, then there is a
unique index where the indicator is `1`. -/
lemma exists_unique_of_sum_eq_one {n : ℕ} (v : Fin n → ℕ)
    (hb : ∀ i, v i = 0 ∨ v i = 1) (hsum : ∑ i : Fin n, v i = 1) :
    ∃ ℓ : Fin n, v ℓ = 1 ∧ ∀ k : Fin n, k ≠ ℓ → v k = 0 := by
  have hne : ∃ ℓ : Fin n, v ℓ = 1 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ i : Fin n, v i = 0 := by
      intro i; rcases hb i with h | h
      · exact h
      · exact absurd h (hcon i)
    rw [Finset.sum_congr rfl (fun i _ => hall i)] at hsum
    simp at hsum
  obtain ⟨ℓ, hℓ⟩ := hne
  refine ⟨ℓ, hℓ, ?_⟩
  intro k hk
  rcases hb k with h | h
  · exact h
  · exfalso
    have hle : v ℓ + v k ≤ ∑ i : Fin n, v i := by
      have : ({ℓ, k} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
      calc v ℓ + v k = ∑ i ∈ ({ℓ, k} : Finset (Fin n)), v i := by
              rw [Finset.sum_pair hk.symm]
        _ ≤ ∑ i : Fin n, v i := Finset.sum_le_sum_of_subset this
    rw [hsum, hℓ, h] at hle
    omega

/-- `flagLen < circomPrime`. -/
lemma flagLen_lt : flagLen < circomPrime := by
  have h256 : (flagLen : ℕ) = 1025 := rfl
  have h2 : (1024 : ℕ) < 2 ^ 33 := by norm_num
  have hp := factCircomGt2_33.out
  omega

/-- A nat sum of `0/1` indicators over `Fin flagLen` whose `F circomPrime`-cast is
`1` is itself `1` (the sum is small because there are only `flagLen` terms and
`circomPrime` is large). -/
lemma natSum_eq_one_of_cast (g : Fin flagLen → ℕ)
    (hb : ∀ i, g i = 0 ∨ g i = 1)
    (h : ((∑ i : Fin flagLen, g i : ℕ) : F circomPrime) = 1) :
    (∑ i : Fin flagLen, g i) = 1 := by
  have h_small : (∑ i : Fin flagLen, g i) < circomPrime := by
    have hle : (∑ i : Fin flagLen, g i) ≤ ∑ _i : Fin flagLen, 1 := by
      apply Finset.sum_le_sum
      intro i _; rcases hb i with hi | hi <;> omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hle
    have := flagLen_lt
    omega
  exact natCast_eq_one_of_lt h_small h

/-- The soundness math, isolated from the circuit context: boolean flags summing
to one, whose index-weighted sum is `msg`, form the one-hot indicator of
`msg.val < flagLen`. -/
lemma onehot_from_constraints
    (flags : Vector (F circomPrime) flagLen) (msg : F circomPrime)
    (h_bool : ∀ i : Fin flagLen, IsBool flags[i.val])
    (h_sum : (∑ i : Fin flagLen, flags[i.val]) = 1)
    (h_wt : msg = ∑ i : Fin flagLen, flags[i.val] * ((i.val : ℕ) : F circomPrime)) :
    msg.val < flagLen ∧ OneHotAt flags msg.val := by
  -- pass to nat values
  have hv_bool : ∀ i : Fin flagLen,
      (flags[i.val]).val = 0 ∨ (flags[i.val]).val = 1 := fun i => isBool_val _ (h_bool i)
  -- the field sum is the cast of the nat sum
  have h_cast_sum : ((∑ i : Fin flagLen, (flags[i.val]).val : ℕ) : F circomPrime) = 1 := by
    rw [Nat.cast_sum, ← h_sum]
    apply Finset.sum_congr rfl
    intro i _
    rcases h_bool i with h | h <;>
      simp only [h, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one]
  -- so the nat sum is 1
  have h_nat_sum : (∑ i : Fin flagLen, (flags[i.val]).val) = 1 :=
    natSum_eq_one_of_cast (fun i => (flags[i.val]).val) hv_bool h_cast_sum
  -- get the unique one-hot index
  obtain ⟨ℓ, hℓ_one, hℓ_zero⟩ :=
    exists_unique_of_sum_eq_one (fun i => (flags[i.val]).val) hv_bool h_nat_sum
  -- flags is the indicator of ℓ
  have h_indicator : ∀ k : Fin flagLen,
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
  -- msg = (ℓ : F circomPrime)
  have h_term : ∀ i : Fin flagLen,
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
  -- conclude the spec
  have hℓ_lt : ℓ.val < flagLen := ℓ.isLt
  have hℓ_lt_p : ℓ.val < circomPrime := lt_trans hℓ_lt flagLen_lt
  have h_msg_val : msg.val = ℓ.val := by
    rw [h_msg, ZMod.val_natCast_of_lt hℓ_lt_p]
  refine ⟨?_, ?_⟩
  · rw [h_msg_val]; exact hℓ_lt
  · intro k
    rw [h_msg_val]
    exact h_indicator k

end LenFlags
end Solution.JSONExtract
