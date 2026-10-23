import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Mul
import Solution.JSONExtract.Model
import Solution.JSONExtract.Theorems

/-!
# Key matcher for one claim (`JSONExtract`)

`Matcher k` maintains, for the known claim `k`, the register "the key read so
far is a prefix of `k`'s name": it is set at a key start, and on every emitted
code point of the key it is multiplied by `[cp = name_k[kIdx]]`, where the
expected byte is the affine selection of the constant name (padded with an
impossible value) by the key-index one-hot. At a key close it returns the
match flag `keyClose · m · [kIdx = |name_k|]`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Circomlib
open Model (kIdxMax Claim)

namespace Matcher

structure Inputs (F : Type) where
  /-- the emitted code point (`0` when nothing is emitted) -/
  cp : F
  emit : F
  kIdxOH : Vector F kIdxMax
  mPrev : F
  mNext : F
  keyStart : F
  keyClose : F
  /-- the main state before the byte is `KEY` -/
  stKey : F
  active : F
deriving ProvableStruct

def main (k : Claim) (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var field (F circomPrime)) := do
  let expected := Fin.foldl kIdxMax (fun acc t =>
    acc + inp.kIdxOH[t] * (((Model.nameAt k t.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0
  let eq ← IsEqual.circuit (inp.cp, expected)
  let mismatch ← Mul.circuit { a := inp.emit, b := 1 - eq }
  let keep ← Mul.circuit { a := inp.mPrev, b := 1 - mismatch }
  let held ← Mul.circuit { a := inp.stKey, b := keep }
  let d ← Mul.circuit { a := inp.active, b := inp.keyStart + held - inp.mPrev }
  assertZero (inp.mNext - inp.mPrev - d)
  let ℓ : Fin kIdxMax := ⟨(Model.claimName k).length, Model.claimName_length_lt k⟩
  let atLen ← Mul.circuit { a := inp.mPrev, b := inp.kIdxOH[ℓ] }
  Mul.circuit { a := inp.keyClose, b := atLen }

instance elaborated (k : Claim) : ElaboratedCircuit (F circomPrime) Inputs field (main k) := by
  elaborate_circuit

/-- The expected code point at the current key index: the affine selection of
claim `k`'s name by the key-index one-hot (padded with `Model.impossible`). -/
def expected (k : Claim) (kIdxOH : Vector (F circomPrime) kIdxMax) : F circomPrime :=
  Fin.foldl kIdxMax (fun acc t => acc + kIdxOH[t] * (Model.nameAt k t.val : F circomPrime)) 0

/-- The gadget asserts the matcher-register update on its two state inputs, so
the prover must supply an `mNext` that already satisfies it (`mPrev` frozen at an
inactive position, the model's update otherwise).  This is a *prover* assumption
only: for soundness the row itself pins `mNext`, so the caller (`Step`) must not
have to know that `mNext` is honest.  Hence the bundle below is a
`GeneralFormalCircuit` with `Assumptions := True`. -/
def ProverAssumptions (k : Claim) (inp : Inputs (F circomPrime)) : Prop :=
  let eq : F circomPrime := if inp.cp = expected k inp.kIdxOH then 1 else 0
  inp.mNext = inp.mPrev +
    inp.active * (inp.keyStart + inp.stKey * (inp.mPrev * (1 - inp.emit * (1 - eq))) - inp.mPrev)

/-- The two field identities the rows enforce: the matcher register update and
the returned key-match flag. -/
def Spec (k : Claim) (inp : Inputs (F circomPrime)) (out : field (F circomPrime)) : Prop :=
  let eq : F circomPrime := if inp.cp = expected k inp.kIdxOH then 1 else 0
  inp.mNext = inp.mPrev +
      inp.active * (inp.keyStart + inp.stKey * (inp.mPrev * (1 - inp.emit * (1 - eq))) - inp.mPrev) ∧
  let ℓ : Fin kIdxMax := ⟨(Model.claimName k).length, Model.claimName_length_lt k⟩
  out = inp.keyClose * (inp.mPrev * inp.kIdxOH[ℓ])

theorem soundness (k : Claim) :
    GeneralFormalCircuit.Soundness (F circomPrime) (main k) (fun _ _ => True)
      (fun inp out _ => Spec k inp out) := by
  circuit_proof_start [Spec, expected]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_channelsWithRequirements,
    Mul.circuit_output, Mul.circuit_localLength,
    isEqual_Assumptions, isEqual_Spec, isEqual_channelsWithRequirements,
    isEqual_localLength, isEqual_output, Expression.eval,
    true_implies, true_or, and_true] at h_holds ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
  have hOH : ∀ (i : ℕ) (h : i < kIdxMax),
      Expression.eval env (input_var_kIdxOH[i]'h) = input_kIdxOH[i]'h := by
    intro i h
    have := Vector.ext_iff.mp h_input.2.2.1 i h
    simpa [Vector.getElem_map] using this
  have hexp : Expression.eval env
        (Fin.foldl kIdxMax (fun acc t => acc + input_var_kIdxOH[t.val] *
          Expression.const ((Model.nameAt k t.val : ℕ) : F circomPrime)) 0)
      = Fin.foldl kIdxMax
          (fun acc t => acc + input_kIdxOH[t.val] * ((Model.nameAt k t.val : ℕ) : F circomPrime)) 0 := by
    rw [eval_foldl_sum, foldl_add_eq_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Expression.eval]
    rw [hOH t.val t.isLt]
  rw [hexp] at h1
  rw [h1] at h2
  rw [h2] at h3
  rw [h3] at h4
  rw [h4] at h5
  rw [h5] at h6
  rw [hOH _ (Model.claimName_length_lt k)] at h7
  rw [h7] at h8
  -- the first component is the row itself: `h6` pins `mNext`
  rw [sub_sub, sub_eq_zero] at h6
  refine ⟨h6, ?_⟩
  rw [show i₀ + 2 + 1 + 1 + 1 + 1 + 1 = i₀ + 6 + 1 from by omega] at h8
  rw [h8]

theorem completeness (k : Claim) :
    GeneralFormalCircuit.Completeness (F circomPrime) (main k)
      (fun inp _ _ => ProverAssumptions k inp) (fun _ _ _ => True) := by
  circuit_proof_start [ProverAssumptions, expected]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, isEqual_Assumptions, isEqual_Spec,
    true_and, and_true, true_implies, Mul.circuit_output, Mul.circuit_localLength,
    isEqual_localLength, isEqual_output, Expression.eval] at h_env ⊢
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := h_env
  have hOH : ∀ (i : ℕ) (h : i < kIdxMax),
      Expression.eval env.toEnvironment (input_var_kIdxOH[i]'h) = input_kIdxOH[i]'h := by
    intro i h
    have := Vector.ext_iff.mp h_input.2.2.1 i h
    simpa [Vector.getElem_map] using this
  have hexp : Expression.eval env.toEnvironment
        (Fin.foldl kIdxMax (fun acc t => acc + input_var_kIdxOH[t.val] *
          Expression.const ((Model.nameAt k t.val : ℕ) : F circomPrime)) 0)
      = Fin.foldl kIdxMax
          (fun acc t => acc + input_kIdxOH[t.val] * ((Model.nameAt k t.val : ℕ) : F circomPrime)) 0 := by
    rw [eval_foldl_sum, foldl_add_eq_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Expression.eval]
    rw [hOH t.val t.isLt]
  rw [hexp] at h1
  rw [h1] at h2
  rw [h2] at h3
  rw [h3] at h4
  rw [h4] at h5
  rw [h5]
  -- `exact` (not `linear_combination`): the two sides differ only in the `Decidable`
  -- instance of the equality test, which is defeq but not syntactically equal
  rw [sub_sub, sub_eq_zero]
  exact h_assumptions

def circuit (k : Claim) : GeneralFormalCircuit (F circomPrime) Inputs field where
  main := main k
  elaborated := elaborated k
  Assumptions := fun _ _ => True
  Spec := fun inp out _ => Spec k inp out
  ProverAssumptions := fun inp _ _ => ProverAssumptions k inp
  ProverSpec := fun _ _ _ => True
  soundness := soundness k
  completeness := completeness k

end Matcher
end Solution.JSONExtract
