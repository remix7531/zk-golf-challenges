import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Model
import Solution.JSONExtract.Matcher
import Solution.JSONExtract.Interfaces

/-!
# The eleven key matchers of one position (`JSONExtract`)

One `Matcher k` per known claim: it carries the "the key read so far is a
prefix of claim `k`'s name" register across the position and returns the match
flag of a closing key.  The gadget is the loop over the eleven claims.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nClaims kIdxMax Claim)

set_option linter.unusedSimpArgs false

namespace KeyMatchers

structure Inputs (F : Type) where
  /-- the code point emitted at this position -/
  cp : F
  emit : F
  kIdxOH : Vector F kIdxMax
  mPrev : Vector F nClaims
  mNext : Vector F nClaims
  keyStart : F
  keyClose : F
  /-- the main state before the byte is `KEY` -/
  stKey : F
  active : F
deriving ProvableStruct

structure Outputs (F : Type) where
  /-- the key closing at this position is claim `k` -/
  match_ : Vector F nClaims
deriving ProvableStruct

-- as in `Step`: `circuit_norm` would otherwise reduce the concrete name fold of
-- `Matcher.main` for the constant-length side goal of `Circuit.mapFinRange`
attribute [local irreducible] Matcher.main

def main (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let matchOut ← Circuit.mapFinRange nClaims fun kc =>
    Matcher.circuit kc {
      cp := inp.cp, emit := inp.emit, kIdxOH := inp.kIdxOH, mPrev := inp.mPrev[kc],
      mNext := inp.mNext[kc], keyStart := inp.keyStart, keyClose := inp.keyClose,
      stKey := inp.stKey, active := inp.active }
  return { match_ := matchOut }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit

/-- The byte matched claim `k`'s expected code point. -/
def eqCp (k : Claim) (inp : Inputs (F circomPrime)) : F circomPrime :=
  if inp.cp = Matcher.expected k inp.kIdxOH then 1 else 0

/-- The index at which claim `k`'s name is complete. -/
def kLen (k : Claim) : Fin kIdxMax := ⟨(Model.claimName k).length, Model.claimName_length_lt k⟩

/-- The matcher-register update row of every claim. -/
def MRow (inp : Inputs (F circomPrime)) : Prop :=
  ∀ k : Claim, inp.mNext[k.val] = inp.mPrev[k.val] + inp.active *
    (inp.keyStart + inp.stKey * (inp.mPrev[k.val] * (1 - inp.emit * (1 - eqCp k inp)))
      - inp.mPrev[k.val])

/-- The returned match flag of every claim. -/
def MatchOf (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  ∀ k : Claim, out.match_[k.val] = inp.keyClose * (inp.mPrev[k.val] * inp.kIdxOH[(kLen k).val])

def Spec (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  MRow inp ∧ MatchOf inp out

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main (fun _ _ => True)
      (fun inp out _ => Spec inp out) := by
  circuit_proof_start [Spec, MRow, MatchOf, eqCp, kLen, main]
  obtain ⟨e_cp, e_emit, e_kIdxOH, e_mPrev, e_mNext, e_keyStart, e_keyClose, e_stKey,
    e_active⟩ := h_input
  have hmP : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env (input_var_mPrev[i]'h) = input_mPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_mPrev i h
    simpa [Vector.getElem_map] using this
  have hmN : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env (input_var_mNext[i]'h) = input_mNext[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_mNext i h
    simpa [Vector.getElem_map] using this
  simp only [matcher_Assumptions, matcher_Spec, matcher_localLength, matcher_output,
    matcher_channelsWithRequirements, Matcher.Spec, true_implies, true_or, and_true,
    and_self, Vector.getElem_mapFinRange, Fin.getElem_fin, Expression.eval, Nat.add_assoc,
    hmP, hmN, e_cp, e_emit, e_kIdxOH, e_keyStart, e_keyClose, e_stKey,
    e_active] at h_holds ⊢
  exact ⟨⟨fun k => (h_holds k).1, fun k => (h_holds k).2⟩, fun _ => trivial⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      (fun inp _ _ => MRow inp) (fun _ _ _ => True) := by
  circuit_proof_start [MRow, eqCp, main]
  obtain ⟨e_cp, e_emit, e_kIdxOH, e_mPrev, e_mNext, e_keyStart, e_keyClose, e_stKey,
    e_active⟩ := h_input
  have hmP : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env.toEnvironment (input_var_mPrev[i]'h) = input_mPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_mPrev i h
    simpa [Vector.getElem_map] using this
  have hmN : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env.toEnvironment (input_var_mNext[i]'h) = input_mNext[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_mNext i h
    simpa [Vector.getElem_map] using this
  simp only [matcher_ProverAssumptions, matcher_ProverSpec, matcher_localLength,
    matcher_output, Matcher.ProverAssumptions, true_and, and_true, true_implies,
    Vector.getElem_mapFinRange, Fin.getElem_fin, Expression.eval, Nat.add_assoc,
    hmP, hmN, e_cp, e_emit, e_kIdxOH, e_keyStart, e_keyClose, e_stKey,
    e_active] at h_env ⊢
  exact fun k => h_assumptions k

def circuit : GeneralFormalCircuit (F circomPrime) Inputs Outputs where
  main; elaborated
  Assumptions := fun _ _ => True
  Spec := fun inp out _ => Spec inp out
  ProverAssumptions := fun inp _ _ => MRow inp
  ProverSpec := fun _ _ _ => True
  soundness; completeness

end KeyMatchers
end Solution.JSONExtract
