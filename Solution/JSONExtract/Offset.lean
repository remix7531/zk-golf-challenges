import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.Model
import Solution.JSONExtract.Rows
import Solution.JSONExtract.OneHotInterface
import Solution.JSONExtract.Theorems

/-!
# The value offset of one position (`JSONExtract`)

The offset register counts the value characters emitted so far in the current
value: it is cleared outside a value (`inVal = 0`), incremented on every
emitted value character and saturates at `ofsMax - 1`.  The gadget returns the
offset's one-hot indicator, which the ten output slots select their cell with.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (ofsMax)

set_option linter.unusedSimpArgs false

namespace Offset

structure Inputs (F : Type) where
  ofsPrev : F
  ofsNext : F
  /-- a value character is emitted at this position -/
  vEmit : F
  /-- a value is being read (so the offset is kept rather than cleared) -/
  inVal : F
  active : F
deriving ProvableStruct

structure Outputs (F : Type) where
  ofsOH : Vector F ofsMax
deriving ProvableStruct

open Rows (mul freeze)

def main (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let ofsOH ← OneHot.circuit ofsMax { x := inp.ofsPrev }
  let oInc ← mul inp.vEmit (1 - ofsOH[ofsMax - 1])
  let ofsKept ← mul inp.inVal inp.ofsPrev
  freeze inp.active inp.ofsPrev (ofsKept + oInc) inp.ofsNext
  return { ofsOH := ofsOH }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit

/-- The offset update row, written against the one-hot of `ofsPrev`. -/
def OfsRow (inp : Inputs (F circomPrime)) : Prop :=
  inp.ofsNext = inp.ofsPrev + inp.active *
    (inp.inVal * inp.ofsPrev + inp.vEmit * (1 - (ohOf ofsMax inp.ofsPrev)[ofsMax - 1])
      - inp.ofsPrev)

/-- The one-hot gadget needs its input in range. -/
def Assumptions (inp : Inputs (F circomPrime)) : Prop := inp.ofsPrev.val < ofsMax

def Spec (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  out.ofsOH = ohOf ofsMax inp.ofsPrev ∧ OfsRow inp

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main (fun inp _ => Assumptions inp)
      (fun inp out _ => Spec inp out) := by
  circuit_proof_start [Assumptions, Spec, OfsRow, main, mul, freeze]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, Mul.circuit_channelsWithRequirements, oneHot_Assumptions,
    oneHot_Spec_iff, oneHot_localLength, oneHot_output, oneHot_channelsWithRequirements,
    ProvableType.varFromOffset_fields,
    true_implies, true_or, and_true, Expression.eval] at h_holds ⊢
  obtain ⟨hOH, h2, h3, ⟨h4, h5⟩⟩ := h_holds
  obtain ⟨hlt, hOHeq⟩ := hOH ⟨by decide, h_assumptions⟩
  have hOHi := Vector.ext_iff.mp hOHeq
  simp only [Vector.getElem_map] at hOHi
  refine ⟨hOHeq, ?_⟩
  rw [hOHi (ofsMax - 1) (by decide)] at h2
  rw [h2, h3] at h4
  rw [h4] at h5
  linear_combination h5

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      (fun inp _ _ => Assumptions inp ∧ OfsRow inp) (fun _ _ _ => True) := by
  circuit_proof_start [Assumptions, OfsRow, main, mul, freeze]
  obtain ⟨hlt, hrow⟩ := h_assumptions
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, oneHot_Assumptions, oneHot_Spec_iff, oneHot_localLength,
    oneHot_output, true_and, and_true, true_implies, Expression.eval] at h_env ⊢
  obtain ⟨hOH, h2, h3, h4⟩ := h_env
  obtain ⟨-, hOHeq⟩ := hOH ⟨by decide, hlt⟩
  have hOHi := Vector.ext_iff.mp hOHeq
  simp only [Vector.getElem_map] at hOHi
  refine ⟨⟨by decide, hlt⟩, ?_⟩
  rw [hOHi (ofsMax - 1) (by decide)] at h2
  rw [h2, h3] at h4
  rw [h4]
  linear_combination hrow

def circuit : GeneralFormalCircuit (F circomPrime) Inputs Outputs where
  main; elaborated
  Assumptions := fun inp _ => Assumptions inp
  Spec := fun inp out _ => Spec inp out
  ProverAssumptions := fun inp _ _ => Assumptions inp ∧ OfsRow inp
  ProverSpec := fun _ _ _ => True
  soundness; completeness

end Offset
end Solution.JSONExtract
