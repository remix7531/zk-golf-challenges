import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit

/-!
# Witnessed field multiplication (`JSONExtract`)

`Mul` turns a product of two affine circuit expressions into an affine output:
it witnesses the product and pins it with one R1CS row.  The JSON extractor
uses this small gadget when a larger equation would otherwise contain multiple
products (or a product of a product).
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

namespace Mul

/-- The two field factors. -/
structure Inputs (F : Type) where
  a : F
  b : F
deriving ProvableStruct

/-- Witness `a * b` and constrain the witness by one multiplication row. -/
def main (input : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var field (F circomPrime)) := do
  let product ← Circuit.witnessField (input.a * input.b)
  assertZero (product - input.a * input.b)
  return product

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs field main := by
  elaborate_circuit

/-- Field multiplication has no precondition. -/
def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

/-- The returned affine variable is the product of the two inputs. -/
def Spec (input : Inputs (F circomPrime)) (out : field (F circomPrime)) : Prop :=
  out = input.a * input.b

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Spec]
  have h : (env.get i₀ : F circomPrime) = input_a * input_b :=
    sub_eq_zero.mp h_holds
  exact h

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [main]
  rw [h_env]
  ring

/-- The reusable formal-circuit bundle for a witnessed product. -/
def circuit : FormalCircuit (F circomPrime) Inputs field where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Mul
end Solution.JSONExtract
