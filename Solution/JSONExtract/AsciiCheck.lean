import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Model
import Solution.JSONExtract.Rows
import Solution.JSONExtract.Interfaces

/-!
# A routed string code point is ASCII (`JSONExtract`)

A code point that is written into a string claim's slot must be a single
ASCII byte: the slot is a byte array, so a `\uXXXX` escape above `0x7F` or a
raw UTF-8 sequence (which emits the marker `0x80`) is rejected.  One
`LessThan 16` comparison, one witnessed product and the row that ties them.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Circomlib

set_option linter.unusedSimpArgs false

namespace AsciiCheck

structure Inputs (F : Type) where
  /-- the code point emitted at this position -/
  cp : F
  /-- the emitted value is routed into a slot -/
  write : F
  /-- the main state before the byte is `STR` -/
  stStr : F
deriving ProvableStruct

open Rows (mul)

def main (inp : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let lt ← LessThan.circuit 16 two_pow_17_lt (inp.cp, 0x80)
  let ws ← mul inp.write inp.stStr
  assertZero (ws * (1 - lt))

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

/-- `LessThan 16` needs its left argument in range; the caller gets the bound
from the shape of the code point. -/
def Assumptions (inp : Inputs (F circomPrime)) : Prop := inp.cp.val < 2 ^ 16

/-- A written string code point is below `0x80`. -/
def Spec (inp : Inputs (F circomPrime)) : Prop :=
  inp.write * inp.stStr * (1 - (if inp.cp.val < 128 then 1 else 0)) = 0

theorem val_128 : ((128 : F circomPrime)).val = 128 := by
  have h : (128 : F circomPrime) = ((128 : ℕ) : F circomPrime) := by norm_num
  rw [h, ZMod.val_natCast_of_lt (by decide)]

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, main, mul]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, Mul.circuit_channelsWithRequirements, lessThan_Assumptions,
    lessThan_Spec, lessThan_localLength, lessThan_output, lessThan_channelsWithRequirements,
    ProvableType.eval_fieldPair, true_implies, true_or, and_true, Expression.eval] at h_holds ⊢
  obtain ⟨hlt, hws, hrow⟩ := h_holds
  have hA : ZMod.val (128 : F circomPrime) ≤ 2 ^ 16 := by rw [val_128]; norm_num
  have h := hlt ⟨h_assumptions, hA⟩
  rw [val_128] at h
  rw [h, hws] at hrow
  exact hrow

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, main, mul]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, lessThan_Assumptions, lessThan_Spec, lessThan_localLength,
    lessThan_output, ProvableType.eval_fieldPair, true_and, and_true, true_implies,
    Expression.eval] at h_env ⊢
  obtain ⟨hlt, hws⟩ := h_env
  have hA : ZMod.val (128 : F circomPrime) ≤ 2 ^ 16 := by rw [val_128]; norm_num
  have h := hlt ⟨h_assumptions, hA⟩
  rw [val_128] at h
  refine ⟨⟨h_assumptions, hA⟩, ?_⟩
  rw [hws, h]
  exact h_spec

def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end AsciiCheck
end Solution.JSONExtract
