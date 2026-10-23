import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.Model
import Solution.JSONExtract.Rows
import Solution.JSONExtract.Theorems

/-!
# The decoded code point and the `\uXXXX` accumulator (`JSONExtract`)

Given the four emission flags of a position (`Emit`), the byte and its hex
classes, this gadget decodes the code point the position emits and advances
the four-digit hex accumulator of a `\uXXXX` escape.

`hexVal` is the value of a hex digit (three witnessed products, zero off the
hex classes); `cp` picks the byte itself, the escape's code point, the decoded
`\uXXXX` value or the non-ASCII marker according to which emission flag is
set; the accumulator is frozen unless the sub-automaton is inside the first
three hex digits (`inH`).

`escVal` arrives as a single affine input: it is the constant-weighted sum of
the eight simple-escape byte flags, which the caller already has.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

set_option linter.unusedSimpArgs false

namespace CodePoint

structure Inputs (F : Type) where
  byte : F
  isDigit : F
  isUpperHex : F
  isLowerHex : F
  /-- the code point of a simple escape (`0` off the escape class) -/
  escVal : F
  emitPlain : F
  emitEsc : F
  emitU : F
  emitUtf8 : F
  /-- the sub-automaton is reading one of the first three hex digits -/
  inH : F
  hexAccPrev : F
  hexAccNext : F
  active : F
deriving ProvableStruct

structure Outputs (F : Type) where
  /-- the code point emitted at this position (`0` when nothing is emitted) -/
  cp : F
deriving ProvableStruct

open Rows (mul freeze)

def main (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let hvDigit ← mul inp.isDigit (inp.byte - 0x30)
  let hvUpper ← mul inp.isUpperHex (inp.byte - 0x37)
  let hvLower ← mul inp.isLowerHex (inp.byte - 0x57)
  let hexVal := hvDigit + hvUpper + hvLower
  let cpPlain ← mul inp.emitPlain inp.byte
  let cpEsc ← mul inp.emitEsc inp.escVal
  let cpU ← mul inp.emitU (16 * inp.hexAccPrev + hexVal)
  let cp := cpPlain + cpEsc + cpU + 0x80 * inp.emitUtf8
  let hexAccNew ← mul inp.inH (16 * inp.hexAccPrev + hexVal)
  freeze inp.active inp.hexAccPrev hexAccNew inp.hexAccNext
  return { cp := cp }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit

/-- The value of the hex digit the byte stands for (`0` off the hex classes). -/
def hvOf (inp : Inputs (F circomPrime)) : F circomPrime :=
  inp.isDigit * (inp.byte - 0x30) + inp.isUpperHex * (inp.byte - 0x37)
    + inp.isLowerHex * (inp.byte - 0x57)

/-- The accumulator row: frozen off the hex states, `16 · acc + digit` on them. -/
def HexAccRow (inp : Inputs (F circomPrime)) : Prop :=
  inp.hexAccNext = inp.hexAccPrev +
    inp.active * (inp.inH * (16 * inp.hexAccPrev + hvOf inp) - inp.hexAccPrev)

/-- The returned code point and the accumulator row. -/
def Spec (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  out.cp = inp.emitPlain * inp.byte + inp.emitEsc * inp.escVal
      + inp.emitU * (16 * inp.hexAccPrev + hvOf inp) + 0x80 * inp.emitUtf8 ∧
  HexAccRow inp

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main (fun _ _ => True)
      (fun inp out _ => Spec inp out) := by
  circuit_proof_start [Spec, HexAccRow, hvOf, main, mul, freeze]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, Mul.circuit_channelsWithRequirements, true_implies, true_or,
    and_true, Expression.eval] at h_holds ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, ⟨h8, h9⟩⟩ := h_holds
  rw [h1, h2, h3] at h6 h7
  rw [h7] at h8
  constructor
  · rw [h4, h5, h6]
  · rw [h8] at h9
    linear_combination h9

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      (fun inp _ _ => HexAccRow inp) (fun _ _ _ => True) := by
  circuit_proof_start [HexAccRow, hvOf, main, mul, freeze]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, true_and, and_true, true_implies, Expression.eval] at h_env ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_env
  rw [h1, h2, h3] at h7
  rw [h7] at h8
  rw [h8]
  linear_combination h_assumptions

def circuit : GeneralFormalCircuit (F circomPrime) Inputs Outputs where
  main; elaborated
  Assumptions := fun _ _ => True
  Spec := fun inp out _ => Spec inp out
  ProverAssumptions := fun inp _ _ => HexAccRow inp
  ProverSpec := fun _ _ _ => True
  soundness; completeness

end CodePoint
end Solution.JSONExtract
