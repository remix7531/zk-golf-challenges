import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Model
import Solution.JSONExtract.OneHotTheorems

/-!
# Acceptance of the run (`JSONExtract`)

After the last position the main state must be `END`, the sub-state `PLAIN`
(no open string), and at most `maxMembers` members may have been started
(enforced by a `maxMembers + 1`-wide one-hot of the member counter).

The one-hot rows are written out inline rather than delegated to
`OneHot.circuit`: as a subcircuit its `Spec` would only be available under its
own `Assumptions` (`nMem.val < maxMembers + 1`), so the cap in this assertion's
`Spec` would be inherited from an assumption instead of being forced by the
rows, and `Main.soundness` (where a cheating prover picks `nMem`) could never
discharge it. Inlined, `Assumptions` is `True` and the cap comes out of the
constraints. The rows are copied verbatim from `OneHot.main`, so the cost is
unchanged.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSt nSub maxMembers)

namespace Acceptance

structure Inputs (F : Type) where
  st : Vector F nSt
  sub : Vector F nSub
  nMem : F
deriving ProvableStruct

/-- Width of the member-counter one-hot. -/
@[reducible] def memWidth : ℕ := maxMembers + 1

open Model.St Model.Sub in
def main (inp : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  assertZero (inp.st[END] - 1)
  assertZero (inp.sub[PLAIN] - 1)
  -- `OneHot memWidth` of the member counter, inlined (see the module docstring)
  let flags ← Circuit.witnessVector memWidth
    (.range memWidth fun i => (i =? inp.nMem.val).toField)
  Circuit.forEach (Vector.finRange memWidth) fun i => assertZero (flags[i] * (flags[i] - 1))
  assertZero ((Fin.foldl memWidth (fun acc i => acc + flags[i]) 0) - 1)
  assertZero (inp.nMem - Fin.foldl memWidth (fun acc i =>
    acc + flags[i] * (((i.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0)

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

def Assumptions (_inp : Inputs (F circomPrime)) : Prop := True

open Model.St Model.Sub in
def Spec (inp : Inputs (F circomPrime)) : Prop :=
  inp.st[END] = 1 ∧ inp.sub[PLAIN] = 1 ∧ inp.nMem.val ≤ maxMembers

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨e_st, e_sub, -⟩ := h_input
  subst e_st; subst e_sub
  obtain ⟨h1, h2, h_bool_raw, h_sum_raw, h_wt_raw⟩ := h_holds
  have hn : memWidth < circomPrime := by norm_num [memWidth, maxMembers, circomPrime]
  set flags : Vector (F circomPrime) memWidth :=
    Vector.ofFn (fun i : Fin memWidth => env.get (i₀ + i.val)) with hflags
  have hget : ∀ i : Fin memWidth, flags[i.val] = env.get (i₀ + i.val) := by
    intro i; simp [hflags]
  have h_bool : ∀ i : Fin memWidth, IsBool flags[i.val] := by
    intro i
    rw [hget i, IsBool.iff_mul_sub_one]
    exact h_bool_raw i
  have h_sum : (∑ i : Fin memWidth, flags[i.val]) = 1 := by
    rw [LenFlags.eval_foldl_sum] at h_sum_raw
    simp only [Expression.eval, sub_eq_zero] at h_sum_raw
    rw [← h_sum_raw]
    exact Finset.sum_congr rfl (fun i _ => hget i)
  have h_wt : input_nMem = ∑ i : Fin memWidth, flags[i.val] * ((i.val : ℕ) : F circomPrime) := by
    rw [LenFlags.eval_foldl_sum] at h_wt_raw
    simp only [Expression.eval, sub_eq_zero] at h_wt_raw
    rw [h_wt_raw]
    exact Finset.sum_congr rfl (fun i _ => by rw [hget i])
  obtain ⟨h_lt, -⟩ := OneHot.onehot_from_constraints hn flags input_nMem h_bool h_sum h_wt
  refine ⟨?_, ?_, ?_⟩
  · rw [Vector.getElem_map]; exact sub_eq_zero.mp h1
  · rw [Vector.getElem_map]; exact sub_eq_zero.mp h2
  · simp only [memWidth] at h_lt; omega

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨e_st, e_sub, -⟩ := h_input
  subst e_st; subst e_sub
  obtain ⟨s1, s2, s_cap⟩ := h_spec
  rw [Vector.getElem_map] at s1 s2
  have h_lt : input_nMem.val < memWidth := by simp only [memWidth, maxMembers, Specs.JSONExtract.maxMembers] at s_cap ⊢; omega
  have hmod : ∀ m : ℕ, m < memWidth → m % 2 ^ 64 = m := by
    intro m hm
    exact Nat.mod_eq_of_lt (by simp only [memWidth, maxMembers, Specs.JSONExtract.maxMembers] at hm; omega)
  have hg : ∀ i : Fin memWidth,
      env.get (i₀ + i.val) = if i.val = input_nMem.val then (1 : F circomPrime) else 0 := by
    intro i
    rw [h_env i, hmod i.val i.isLt, hmod _ h_lt]
  refine ⟨sub_eq_zero.mpr s1, sub_eq_zero.mpr s2, fun i => ?_, ?_, ?_⟩
  · rw [hg i]; by_cases h : i.val = input_nMem.val <;> simp [h]
  · rw [LenFlags.eval_foldl_sum]
    have : (∑ i : Fin memWidth, Expression.eval env.toEnvironment (var { index := i₀ + i.val }))
        = (1 : F circomPrime) := by
      simp only [Expression.eval]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hg i)]
      rw [Finset.sum_eq_single (⟨input_nMem.val, h_lt⟩ : Fin memWidth)]
      · simp
      · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]; ring
  · rw [LenFlags.eval_foldl_sum]
    have hsum : (∑ i : Fin memWidth, Expression.eval env.toEnvironment
          (var { index := i₀ + i.val } * Expression.const ((i.val : ℕ) : F circomPrime)))
        = ((input_nMem.val : ℕ) : F circomPrime) := by
      have hstep : ∀ i : Fin memWidth, Expression.eval env.toEnvironment
            (var { index := i₀ + i.val } * Expression.const ((i.val : ℕ) : F circomPrime))
          = (if i.val = input_nMem.val then (1 : F circomPrime) else 0)
              * ((i.val : ℕ) : F circomPrime) := by
        intro i; simp only [Expression.eval]; rw [hg i]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i)]
      rw [Finset.sum_eq_single (⟨input_nMem.val, h_lt⟩ : Fin memWidth)]
      · simp
      · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, ZMod.natCast_val, ZMod.cast_id]
    ring

def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end Acceptance
end Solution.JSONExtract
