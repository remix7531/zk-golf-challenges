import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.Model
import Solution.JSONExtract.Rows
import Solution.JSONExtract.Theorems

/-!
# The value characters of one position (`JSONExtract`)

A position emits a *value* character when it emits a string code point inside
`STR`, or when it reads a decimal digit of an integer value.  The emitted
value is routed into an output slot when the claim register says a known
string or integer claim is being read (`kStrInt = kStr + kInt`).

Five witnessed rows: the two emission flags, the routing gate `write`, and the
two halves of the routed value.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

set_option linter.unusedSimpArgs false

namespace ValueEmit

structure Inputs (F : Type) where
  /-- a code point is emitted at this position -/
  emit : F
  /-- the main state before the byte is `STR` -/
  stStr : F
  isDigit : F
  /-- the main state before the byte is one of `PVAL`, `NSIGN`, `NINT` -/
  stNum : F
  /-- the claim register says a known string or integer claim is being read -/
  kStrInt : F
  /-- the code point emitted at this position -/
  cp : F
  byte : F
deriving ProvableStruct

structure Outputs (F : Type) where
  strEmit : F
  digitEmit : F
  /-- the routed-value gate -/
  write : F
  /-- the routed value -/
  valOut : F
deriving ProvableStruct

open Rows (mul)

def main (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let strEmit ← mul inp.emit inp.stStr
  let digitEmit ← mul inp.isDigit inp.stNum
  let vEmit := strEmit + digitEmit
  let write ← mul vEmit inp.kStrInt
  let voStr ← mul strEmit inp.cp
  let voDigit ← mul digitEmit (inp.byte - 0x30)
  return { strEmit := strEmit, digitEmit := digitEmit, write := write,
           valOut := voStr + voDigit }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

def Spec (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  out.strEmit = inp.emit * inp.stStr ∧
  out.digitEmit = inp.isDigit * inp.stNum ∧
  out.write = (out.strEmit + out.digitEmit) * inp.kStrInt ∧
  out.valOut = out.strEmit * inp.cp + out.digitEmit * (inp.byte - 0x30)

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, main, mul]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, Mul.circuit_channelsWithRequirements, true_implies, true_or,
    and_true, Expression.eval] at h_holds ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h_holds
  exact ⟨h1, h2, h3, by rw [h4, h5]⟩

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Assumptions, main, mul]
  simp only [Mul.circuit_Assumptions]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

def circuit : FormalCircuit (F circomPrime) Inputs Outputs where
  main; elaborated; Assumptions; Spec; soundness; completeness

end ValueEmit
end Solution.JSONExtract
