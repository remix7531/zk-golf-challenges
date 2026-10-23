import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Model
import Mathlib.Tactic.LinearCombination

/-!
# The claim register's shape and the four kind flags (`JSONExtract`)

A `FormalAssertion` over the two per-claim registers a position reads: it
pins every entry of `claimPrev` and of `mPrev` boolean, and pins the "no
known claim" flag `kUnk = 1 − kStr − kInt − kBool` boolean, which is what
forces *at most one* claim flag to be set (two set flags would make `kUnk`
equal `-1`).

`kStr`/`kInt`/`kBool`/`kUnk` are the type gates the main automaton reads;
they are affine selections of the claim register, so they live here next to
the row that makes them meaningful.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nClaims Claim)

set_option linter.unusedSimpArgs false

namespace ClaimKinds

abbrev E := Expression (F circomPrime)

structure Inputs (F : Type) where
  /-- the claim register before the byte -/
  claimPrev : Vector F nClaims
  /-- the key-matcher registers before the byte -/
  mPrev : Vector F nClaims
deriving ProvableStruct

/-! ## The four kind flags -/

/-- A string claim is being read. -/
def kStrE (cl : Vector E nClaims) : E :=
  cl[0] + cl[1] + cl[2] + cl[3] + cl[4] + cl[5] + cl[7] + cl[8]
/-- An integer claim is being read. -/
def kIntE (cl : Vector E nClaims) : E := cl[9] + cl[10]
/-- The boolean claim is being read. -/
def kBoolE (cl : Vector E nClaims) : E := cl[6]
/-- No known claim is being read. -/
def kUnkE (cl : Vector E nClaims) : E := 1 - kStrE cl - kIntE cl - kBoolE cl

/-- The value-level twin of `kStrE`. -/
def kStr (cl : Vector (F circomPrime) nClaims) : F circomPrime :=
  cl[0] + cl[1] + cl[2] + cl[3] + cl[4] + cl[5] + cl[7] + cl[8]
/-- The value-level twin of `kIntE`. -/
def kInt (cl : Vector (F circomPrime) nClaims) : F circomPrime := cl[9] + cl[10]
/-- The value-level twin of `kBoolE`. -/
def kBool (cl : Vector (F circomPrime) nClaims) : F circomPrime := cl[6]
/-- The value-level twin of `kUnkE`. -/
def kUnk (cl : Vector (F circomPrime) nClaims) : F circomPrime := 1 - kStr cl - kInt cl - kBool cl

def main (inp : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  Circuit.forEach (Vector.finRange nClaims) fun kc =>
    assertZero (inp.claimPrev[kc] * (inp.claimPrev[kc] - 1))
  Circuit.forEach (Vector.finRange nClaims) fun kc =>
    assertZero (inp.mPrev[kc] * (inp.mPrev[kc] - 1))
  assertZero (kUnkE inp.claimPrev * (kUnkE inp.claimPrev - 1))

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

/-- Both registers are boolean and at most one claim flag is set. -/
def Spec (inp : Inputs (F circomPrime)) : Prop :=
  (∀ k : Claim, IsBool inp.claimPrev[k.val]) ∧
  (∀ k : Claim, IsBool inp.mPrev[k.val]) ∧
  IsBool (kUnk inp.claimPrev)

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨e_claimPrev, e_mPrev⟩ := h_input
  have hcl : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env (input_var_claimPrev[i]'h) = input_claimPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_claimPrev i h
    simpa [Vector.getElem_map] using this
  have hm : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env (input_var_mPrev[i]'h) = input_mPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_mPrev i h
    simpa [Vector.getElem_map] using this
  obtain ⟨h_cl, h_m, h_unk⟩ := h_holds
  simp only [Vector.getElem_finRange, Fin.getElem_fin, Expression.eval, hcl, hm] at h_cl h_m h_unk
  simp only [kUnkE, kStrE, kIntE, kBoolE, Expression.eval, eval_sub, eval_add,
    eval_mul, eval_neg, hcl] at h_unk
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · exact IsBool.iff_mul_sub_one.mpr (h_cl k)
  · exact IsBool.iff_mul_sub_one.mpr (h_m k)
  · rw [IsBool.iff_mul_sub_one]
    simp only [kUnk, kStr, kInt, kBool]
    linear_combination h_unk

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨e_claimPrev, e_mPrev⟩ := h_input
  have hcl : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env.toEnvironment (input_var_claimPrev[i]'h) = input_claimPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_claimPrev i h
    simpa [Vector.getElem_map] using this
  have hm : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env.toEnvironment (input_var_mPrev[i]'h) = input_mPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_mPrev i h
    simpa [Vector.getElem_map] using this
  obtain ⟨s_cl, s_m, s_unk⟩ := h_spec
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · simp only [Vector.getElem_finRange, Fin.getElem_fin, Expression.eval, hcl]
    rcases s_cl k with h | h <;> rw [h] <;> ring
  · simp only [Vector.getElem_finRange, Fin.getElem_fin, Expression.eval, hm]
    rcases s_m k with h | h <;> rw [h] <;> ring
  · have := IsBool.iff_mul_sub_one.mp s_unk
    simp only [kUnk, kStr, kInt, kBool] at this
    simp only [kUnkE, kStrE, kIntE, kBoolE, Expression.eval, eval_sub, eval_add,
      eval_mul, eval_neg, hcl]
    linear_combination this

def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end ClaimKinds
end Solution.JSONExtract
