import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Model

/-!
# Anchoring the run at position 0 (`JSONExtract`)

The state and registers before the first byte are the initial state of the
automaton: main state `PRE`, sub-state `PLAIN`, every counter and register
zero, no matcher set, no claim selected, and the prefix sum of the length
flags zero.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSt nSub nClaims)

namespace Anchors

structure Inputs (F : Type) where
  accm : F
  st : Vector F nSt
  sub : Vector F nSub
  hexAcc : F
  kIdx : F
  ofs : F
  nMem : F
  m : Vector F nClaims
  claim : Vector F nClaims
deriving ProvableStruct

open Model.St Model.Sub in
def main (inp : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  assertZero inp.accm
  assertZero (inp.st[PRE] - 1)
  assertZero (inp.sub[PLAIN] - 1)
  assertZero inp.hexAcc
  assertZero inp.kIdx
  assertZero inp.ofs
  assertZero inp.nMem
  Circuit.forEach (Vector.finRange nClaims) fun k => assertZero inp.m[k]
  Circuit.forEach (Vector.finRange nClaims) fun k => assertZero inp.claim[k]

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

open Model.St Model.Sub in
def Spec (inp : Inputs (F circomPrime)) : Prop :=
  inp.accm = 0 ∧ inp.st[PRE] = 1 ∧ inp.sub[PLAIN] = 1 ∧ inp.hexAcc = 0 ∧ inp.kIdx = 0 ∧
  inp.ofs = 0 ∧ inp.nMem = 0 ∧ (∀ k : Fin nClaims, inp.m[k] = 0) ∧ ∀ k : Fin nClaims, inp.claim[k] = 0

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Spec]
  obtain ⟨-, e_st, e_sub, -, -, -, -, e_m, e_claim⟩ := h_input
  subst e_st; subst e_sub; subst e_m; subst e_claim
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h_holds
  refine ⟨h1, ?_, ?_, h4, h5, h6, h7, ?_, ?_⟩
  · rw [Vector.getElem_map]; exact sub_eq_zero.mp h2
  · rw [Vector.getElem_map]; exact sub_eq_zero.mp h3
  · intro k; rw [Vector.getElem_map]; exact h8 k
  · intro k; rw [Vector.getElem_map]; exact h9 k

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Spec]
  obtain ⟨-, e_st, e_sub, -, -, -, -, e_m, e_claim⟩ := h_input
  subst e_st; subst e_sub; subst e_m; subst e_claim
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := h_spec
  rw [Vector.getElem_map] at s2 s3
  refine ⟨s1, sub_eq_zero.mpr s2, sub_eq_zero.mpr s3, s4, s5, s6, s7, ?_, ?_⟩
  · intro k; have := s8 k; rwa [Vector.getElem_map] at this
  · intro k; have := s9 k; rwa [Vector.getElem_map] at this

def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end Anchors
end Solution.JSONExtract
