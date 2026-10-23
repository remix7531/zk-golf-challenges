import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Model
import Solution.JSONExtract.Rows
import Solution.JSONExtract.Theorems

/-!
# The claim register of one position (`JSONExtract`)

The claim register says which known claim's value is being read.  It is set to
the claim a closing key matched (`match_`), cleared at a key start and held
otherwise; like every register it is frozen at an inactive position.  One loop
of two witnessed rows per claim.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nClaims Claim)

set_option linter.unusedSimpArgs false

namespace ClaimReg

structure Inputs (F : Type) where
  active : F
  keyClose : F
  keyStart : F
  /-- the key closing at this position is claim `k` -/
  match_ : Vector F nClaims
  claimPrev : Vector F nClaims
  claimNext : Vector F nClaims
deriving ProvableStruct

open Rows (mul freeze)

def main (inp : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let hold := 1 - inp.keyClose - inp.keyStart
  Circuit.forEach (Vector.finRange nClaims) fun kc => do
    let kept ← mul hold inp.claimPrev[kc]
    freeze inp.active inp.claimPrev[kc] (inp.match_[kc] + kept) inp.claimNext[kc]

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

/-- The claim-register update row of every claim. -/
def Spec (inp : Inputs (F circomPrime)) : Prop :=
  ∀ k : Claim, inp.claimNext[k.val] = inp.claimPrev[k.val] + inp.active *
    (inp.match_[k.val] + (1 - inp.keyClose - inp.keyStart) * inp.claimPrev[k.val]
      - inp.claimPrev[k.val])

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, main, mul, freeze]
  obtain ⟨e_active, e_keyClose, e_keyStart, e_match, e_claimPrev, e_claimNext⟩ := h_input
  have hmt : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env (input_var_match_[i]'h) = input_match_[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_match i h
    simpa [Vector.getElem_map] using this
  have hcP : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env (input_var_claimPrev[i]'h) = input_claimPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_claimPrev i h
    simpa [Vector.getElem_map] using this
  have hcN : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env (input_var_claimNext[i]'h) = input_claimNext[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_claimNext i h
    simpa [Vector.getElem_map] using this
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, Mul.circuit_channelsWithRequirements, true_implies, true_or,
    and_true, Vector.getElem_finRange, Fin.getElem_fin, Expression.eval,
    hmt, hcP, hcN, e_active, e_keyClose, e_keyStart] at h_holds ⊢
  refine ⟨fun k => ?_, fun _ => trivial⟩
  obtain ⟨g1, g2, g3⟩ := h_holds k
  rw [g1] at g2
  rw [g2] at g3
  linear_combination g3

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, main, mul, freeze]
  obtain ⟨e_active, e_keyClose, e_keyStart, e_match, e_claimPrev, e_claimNext⟩ := h_input
  have hmt : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env.toEnvironment (input_var_match_[i]'h) = input_match_[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_match i h
    simpa [Vector.getElem_map] using this
  have hcP : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env.toEnvironment (input_var_claimPrev[i]'h) = input_claimPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_claimPrev i h
    simpa [Vector.getElem_map] using this
  have hcN : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env.toEnvironment (input_var_claimNext[i]'h) = input_claimNext[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_claimNext i h
    simpa [Vector.getElem_map] using this
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, true_and, and_true, true_implies,
    Vector.getElem_finRange, Fin.getElem_fin, Expression.eval,
    hmt, hcP, hcN, e_active, e_keyClose, e_keyStart] at h_env ⊢
  intro k
  obtain ⟨g1, g2⟩ := h_env k
  rw [g1] at g2
  rw [g2]
  linear_combination h_spec k

def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end ClaimReg
end Solution.JSONExtract
