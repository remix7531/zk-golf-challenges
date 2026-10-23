import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.Model
import Solution.JSONExtract.Rows
import Solution.JSONExtract.Theorems

/-!
# The four emission flags of one position (`JSONExtract`)

Inside a string (`inStr = 1`) a byte completes a code point in exactly one of
four ways, according to the sub-automaton state before it: an unescaped byte
in `PLAIN`, a simple escape in `ESC`, the last hex digit in `H4`, the last
continuation byte in `C1`.  Each flag is the product of three signals, so the
gadget first materialises the four `inStr · subPrev[s]` products and then
multiplies each by its byte class: eight witnessed rows.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSub Sub)

set_option linter.unusedSimpArgs false

namespace Emit

open Model.Sub

structure Inputs (F : Type) where
  /-- the main automaton is inside a string (`KEY` or `STR`) -/
  inStr : F
  subPrev : Vector F nSub
  isUnescaped : F
  isSimpleEsc : F
  isHex : F
  isCont : F
deriving ProvableStruct

structure Outputs (F : Type) where
  emitPlain : F
  emitEsc : F
  emitU : F
  emitUtf8 : F
deriving ProvableStruct

open Rows (mul)

def main (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let inPlain ← mul inp.inStr inp.subPrev[PLAIN]
  let inEsc ← mul inp.inStr inp.subPrev[ESC]
  let inH4 ← mul inp.inStr inp.subPrev[H4]
  let inC1 ← mul inp.inStr inp.subPrev[C1]
  let emitPlain ← mul inPlain inp.isUnescaped
  let emitEsc ← mul inEsc inp.isSimpleEsc
  let emitU ← mul inH4 inp.isHex
  let emitUtf8 ← mul inC1 inp.isCont
  return { emitPlain := emitPlain, emitEsc := emitEsc, emitU := emitU, emitUtf8 := emitUtf8 }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

/-- Each emission flag is the triple product of the string gate, the
sub-automaton state it reads and its byte class. -/
def Spec (inp : Inputs (F circomPrime)) (out : Outputs (F circomPrime)) : Prop :=
  out.emitPlain = inp.inStr * inp.subPrev[PLAIN.val] * inp.isUnescaped ∧
  out.emitEsc = inp.inStr * inp.subPrev[ESC.val] * inp.isSimpleEsc ∧
  out.emitU = inp.inStr * inp.subPrev[H4.val] * inp.isHex ∧
  out.emitUtf8 = inp.inStr * inp.subPrev[C1.val] * inp.isCont

theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, main, mul]
  obtain ⟨e_inStr, e_subPrev, e_isUnescaped, e_isSimpleEsc, e_isHex, e_isCont⟩ := h_input
  have hsp : ∀ (i : ℕ) (h : i < nSub),
      Expression.eval env (input_var_subPrev[i]'h) = input_subPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_subPrev i h
    simpa [Vector.getElem_map] using this
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, Mul.circuit_channelsWithRequirements, true_implies, true_or,
    and_true, Expression.eval, Fin.getElem_fin, hsp, e_inStr, e_isUnescaped, e_isSimpleEsc,
    e_isHex, e_isCont] at h_holds ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
  rw [h1] at h5
  rw [h2] at h6
  rw [h3] at h7
  rw [h4] at h8
  exact ⟨h5, h6, h7, h8⟩

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Assumptions, main, mul]
  simp only [Mul.circuit_Assumptions]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

def circuit : FormalCircuit (F circomPrime) Inputs Outputs where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Emit
end Solution.JSONExtract
