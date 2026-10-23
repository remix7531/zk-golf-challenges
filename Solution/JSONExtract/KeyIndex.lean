import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.Model
import Solution.JSONExtract.Rows
import Solution.JSONExtract.OneHotInterface
import Solution.JSONExtract.Theorems

/-!
# The key index and the two key events of one position (`JSONExtract`)

`keyStart` marks a position that enters the `KEY` state from outside it,
`keyClose` a `"` that closes a key.  The key index counts the code points
emitted inside the current key, saturating at `kIdxMax - 1`, and is cleared
outside `KEY`; the gadget also returns its one-hot indicator, which the key
matchers select the expected name byte with.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (kIdxMax)

set_option linter.unusedSimpArgs false

namespace KeyIndex

structure Inputs (F : Type) where
  /-- the main state before the byte is `KEY` -/
  stKeyPrev : F
  /-- the main state after the byte is `KEY` -/
  stKeyNext : F
  /-- a `"` with the sub-automaton in `PLAIN` -/
  closeQuote : F
  /-- a code point is emitted at this position -/
  emit : F
  kIdxPrev : F
  kIdxNext : F
  active : F
deriving ProvableStruct

structure Outputs (F : Type) where
  keyStart : F
  keyClose : F
  kIdxOH : Vector F kIdxMax
deriving ProvableStruct

open Rows (mul freeze)

def main (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let keyStart ← mul inp.stKeyNext (1 - inp.stKeyPrev)
  let keyClose ← mul inp.stKeyPrev inp.closeQuote
  let kIdxOH ← OneHot.circuit kIdxMax { x := inp.kIdxPrev }
  let kInc ← mul inp.emit (1 - kIdxOH[kIdxMax - 1])
  let kIdxNew ← mul inp.stKeyPrev (inp.kIdxPrev + kInc)
  freeze inp.active inp.kIdxPrev kIdxNew inp.kIdxNext
  return { keyStart := keyStart, keyClose := keyClose, kIdxOH := kIdxOH }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit

/-- The key-index update row, written against the one-hot of `kIdxPrev`. -/
def KIdxRow (inp : Inputs (F circomPrime)) : Prop :=
  inp.kIdxNext = inp.kIdxPrev + inp.active *
    (inp.stKeyPrev * (inp.kIdxPrev + inp.emit * (1 - (ohOf kIdxMax inp.kIdxPrev)[kIdxMax - 1]))
      - inp.kIdxPrev)

/-- The one-hot gadget needs its input in range; `Main` supplies it from the
previous position's register bound. -/
def Assumptions (inp : Inputs (F circomPrime)) : Prop := inp.kIdxPrev.val < kIdxMax

def Spec (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  out.keyStart = inp.stKeyNext * (1 - inp.stKeyPrev) ∧
  out.keyClose = inp.stKeyPrev * inp.closeQuote ∧
  out.kIdxOH = ohOf kIdxMax inp.kIdxPrev ∧
  KIdxRow inp

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main (fun inp _ => Assumptions inp)
      (fun inp out _ => Spec inp out) := by
  circuit_proof_start [Assumptions, Spec, KIdxRow, main, mul, freeze]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, Mul.circuit_channelsWithRequirements, oneHot_Assumptions,
    oneHot_Spec_iff, oneHot_localLength, oneHot_output, oneHot_channelsWithRequirements,
    ProvableType.varFromOffset_fields,
    true_implies, true_or, and_true, Expression.eval] at h_holds ⊢
  obtain ⟨h1, h2, hOH, h4, h5, ⟨h6, h7⟩⟩ := h_holds
  obtain ⟨hlt, hOHeq⟩ := hOH ⟨by decide, h_assumptions⟩
  have hOHi := Vector.ext_iff.mp hOHeq
  simp only [Vector.getElem_map] at hOHi
  refine ⟨h1, h2, hOHeq, ?_⟩
  rw [hOHi (kIdxMax - 1) (by decide)] at h4
  rw [h4] at h5
  rw [h5] at h6
  rw [h6] at h7
  linear_combination h7

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      (fun inp _ _ => Assumptions inp ∧ KIdxRow inp) (fun _ _ _ => True) := by
  circuit_proof_start [Assumptions, KIdxRow, main, mul, freeze]
  obtain ⟨hlt, hrow⟩ := h_assumptions
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, oneHot_Assumptions, oneHot_Spec_iff, oneHot_localLength,
    oneHot_output, true_and, and_true, true_implies, Expression.eval] at h_env ⊢
  obtain ⟨h1, h2, hOH, h5, ⟨h6, h7⟩⟩ := h_env
  obtain ⟨-, hOHeq⟩ := hOH ⟨by decide, hlt⟩
  have hOHi := Vector.ext_iff.mp hOHeq
  simp only [Vector.getElem_map] at hOHi
  refine ⟨⟨by decide, hlt⟩, ?_⟩
  rw [hOHi (kIdxMax - 1) (by decide)] at h5
  rw [h5] at h6
  rw [h6] at h7
  rw [h7]
  linear_combination hrow

def circuit : GeneralFormalCircuit (F circomPrime) Inputs Outputs where
  main; elaborated
  Assumptions := fun inp _ => Assumptions inp
  Spec := fun inp out _ => Spec inp out
  ProverAssumptions := fun inp _ _ => Assumptions inp ∧ KIdxRow inp
  ProverSpec := fun _ _ _ => True
  soundness; completeness

end KeyIndex
end Solution.JSONExtract
