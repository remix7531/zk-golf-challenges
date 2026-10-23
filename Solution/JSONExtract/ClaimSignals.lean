import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Model
import Solution.JSONExtract.Rows
import Solution.JSONExtract.Theorems

/-!
# The per-position signals the end pins sum over (`JSONExtract`)

Three per-claim signals leave a position: a value character was emitted for
claim `k`, a `-` was consumed in front of claim `k`'s integer value, and the
`true` literal completed for the boolean claim.  Each is the claim register
gated by the corresponding event.  The member counter is advanced by the same
gadget, since `keyStart` is the event that starts a member.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nClaims Claim)

set_option linter.unusedSimpArgs false

namespace ClaimSignals

structure Inputs (F : Type) where
  /-- a value character is emitted at this position -/
  vEmit : F
  claimPrev : Vector F nClaims
  /-- the main state before the byte is `PVAL` -/
  stPval : F
  isMinus : F
  /-- the main state before the byte is `T3` -/
  stT3 : F
  isLowerE : F
  nMemPrev : F
  nMemNext : F
  /-- a key starts at this position -/
  keyStart : F
deriving ProvableStruct

structure Outputs (F : Type) where
  vEmitK : Vector F nClaims
  minusK : Vector F nClaims
  trueK : F
deriving ProvableStruct

open Rows (mul)

def main (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let vEmitK ← Circuit.mapFinRange nClaims fun kc => mul inp.vEmit inp.claimPrev[kc]
  let minusFlag ← mul inp.stPval inp.isMinus
  let minusK ← Circuit.mapFinRange nClaims fun kc => mul minusFlag inp.claimPrev[kc]
  let trueDone ← mul inp.stT3 inp.isLowerE
  let trueK ← mul trueDone inp.claimPrev[6]
  assertZero (inp.nMemNext - inp.nMemPrev - inp.keyStart)
  return { vEmitK := vEmitK, minusK := minusK, trueK := trueK }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit

/-- The member counter row. -/
def NMemRow (inp : Inputs (F circomPrime)) : Prop :=
  inp.nMemNext = inp.nMemPrev + inp.keyStart

def Spec (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  (∀ k : Claim, out.vEmitK[k.val] = inp.vEmit * inp.claimPrev[k.val]) ∧
  (∀ k : Claim, out.minusK[k.val] = inp.stPval * inp.isMinus * inp.claimPrev[k.val]) ∧
  out.trueK = inp.stT3 * inp.isLowerE * inp.claimPrev[6] ∧
  NMemRow inp

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main (fun _ _ => True)
      (fun inp out _ => Spec inp out) := by
  circuit_proof_start [Spec, NMemRow, main, mul]
  obtain ⟨e_vEmit, e_claimPrev, e_stPval, e_isMinus, e_stT3, e_isLowerE, e_nMemPrev,
    e_nMemNext, e_keyStart⟩ := h_input
  have hcl : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env (input_var_claimPrev[i]'h) = input_claimPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_claimPrev i h
    simpa [Vector.getElem_map] using this
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, Mul.circuit_channelsWithRequirements, true_implies, true_or,
    and_true, and_self, mul_one, Vector.getElem_mapFinRange, Fin.getElem_fin, Expression.eval,
    hcl, e_vEmit, e_stPval, e_isMinus, e_stT3, e_isLowerE, e_nMemPrev, e_nMemNext,
    e_keyStart] at h_holds ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h_holds
  refine ⟨⟨fun k => h1 k, fun k => ?_, ?_, by linear_combination h6⟩, ⟨fun _ => trivial, trivial, fun _ => trivial⟩⟩
  · rw [h3 k, h2]
  · rw [h5, h4]

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      (fun inp _ _ => NMemRow inp) (fun _ _ _ => True) := by
  circuit_proof_start [NMemRow, main, mul]
  obtain ⟨e_vEmit, e_claimPrev, e_stPval, e_isMinus, e_stT3, e_isLowerE, e_nMemPrev,
    e_nMemNext, e_keyStart⟩ := h_input
  simp only [Mul.circuit_Assumptions, true_and, and_true, true_implies,
    Expression.eval, e_nMemPrev, e_nMemNext, e_keyStart] at h_env ⊢
  exact ⟨fun _ => trivial, fun _ => trivial, by linear_combination h_assumptions⟩

def circuit : GeneralFormalCircuit (F circomPrime) Inputs Outputs where
  main; elaborated
  Assumptions := fun _ _ => True
  Spec := fun inp out _ => Spec inp out
  ProverAssumptions := fun inp _ _ => NMemRow inp
  ProverSpec := fun _ _ _ => True
  soundness; completeness

/-! ## The gadget's output block, as `rfl` lemmas -/

@[simp] lemma out_vEmitK (inp : Var Inputs (F circomPrime)) (i : ℕ) :
    (circuit.output inp i).vEmitK = Vector.mapFinRange nClaims (fun k => var ⟨i + k.val⟩) := rfl

@[simp] lemma out_minusK (inp : Var Inputs (F circomPrime)) (i : ℕ) :
    (circuit.output inp i).minusK
      = Vector.mapFinRange nClaims (fun k => var ⟨i + nClaims * 1 + 1 + k.val⟩) := rfl

@[simp] lemma out_trueK (inp : Var Inputs (F circomPrime)) (i : ℕ) :
    (circuit.output inp i).trueK = var ⟨i + nClaims * 1 + 1 + nClaims * 1 + 1⟩ := rfl

end ClaimSignals
end Solution.JSONExtract
