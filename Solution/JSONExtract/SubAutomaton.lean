import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Mul
import Solution.JSONExtract.Model
import Solution.JSONExtract.ByteClass
import Solution.JSONExtract.AutomatonTheorems

/-!
# The string sub-automaton, one position (`JSONExtract`)

A `FormalAssertion` relating the sub-state before a byte to the witnessed
sub-state after it (`Model.stepSub`): inside a string (`inStr = 1`) the next
state is the successor of the edge the byte takes (no edge, no satisfying
successor: the byte is rejected); outside strings the next state is `PLAIN`;
at an inactive position the state is frozen.

The edge products `subPrev[src] · class` are witnessed rows, the successor
mass of each state is their affine sum, and the two gates (`inStr`, `active`)
are one witnessed product each.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSub Sub)

namespace SubAutomaton

structure Inputs (F : Type) where
  inStr : F
  active : F
  cls : ByteClass.Outputs F
  subPrev : Vector F nSub
  subNext : Vector F nSub
deriving ProvableStruct

/-- Byte classes an edge can read. -/
inductive SCls where
  | quote | unescaped | backslash | lead2 | e0 | lead3 | ed | f0 | lead4 | f4
  | simpleEsc | lowerU | hex | cont | contA0BF | cont809F | cont90BF | cont808F
deriving DecidableEq, Repr, Inhabited

structure Edge where
  src : Sub
  cls : SCls
  dst : Sub
deriving Repr, Inhabited

open Model.Sub in
/-- The edges (mirrors `Model.stepSub`). -/
def edges : Vector Edge 23 := #v[
  ⟨PLAIN, .quote, PLAIN⟩, ⟨PLAIN, .unescaped, PLAIN⟩, ⟨PLAIN, .backslash, ESC⟩,
  ⟨PLAIN, .lead2, C1⟩, ⟨PLAIN, .e0, E0s⟩, ⟨PLAIN, .lead3, C2⟩, ⟨PLAIN, .ed, EDs⟩,
  ⟨PLAIN, .f0, F0s⟩, ⟨PLAIN, .lead4, C3⟩, ⟨PLAIN, .f4, F4s⟩,
  ⟨ESC, .simpleEsc, PLAIN⟩, ⟨ESC, .lowerU, H1⟩,
  ⟨H1, .hex, H2⟩, ⟨H2, .hex, H3⟩, ⟨H3, .hex, H4⟩, ⟨H4, .hex, PLAIN⟩,
  ⟨C1, .cont, PLAIN⟩, ⟨C2, .cont, C1⟩, ⟨C3, .cont, C2⟩,
  ⟨E0s, .contA0BF, C1⟩, ⟨EDs, .cont809F, C1⟩, ⟨F0s, .cont90BF, C2⟩, ⟨F4s, .cont808F, C2⟩]

abbrev E := Expression (F circomPrime)

def clsExpr (c : ByteClass.Outputs E) : SCls → E
  | .quote => c.bytes.isQuote | .unescaped => c.classes.isUnescaped
  | .backslash => c.bytes.isBackslash | .lead2 => c.classes.isLead2 | .e0 => c.bytes.isE0
  | .lead3 => c.classes.isLead3 | .ed => c.bytes.isED | .f0 => c.bytes.isF0
  | .lead4 => c.classes.isLead4 | .f4 => c.bytes.isF4 | .simpleEsc => c.classes.isSimpleEsc
  | .lowerU => c.bytes.isLowerU | .hex => c.classes.isHex | .cont => c.classes.isCont
  | .contA0BF => c.classes.isContA0BF | .cont809F => c.classes.isCont809F
  | .cont90BF => c.classes.isCont90BF | .cont808F => c.classes.isCont808F

/-- The sum of the edge products entering state `j`. -/
def mass (prods : Vector E 23) (j : ℕ) : E :=
  Fin.foldl 23 (fun acc e => if (edges[e]).dst.val = j then acc + prods[e] else acc) 0

-- 4.33: `circuit_norm` reduces concrete folds, so the constant-length side goals of
-- `Circuit.forEach` try to evaluate the 23-edge `mass` sum; seal it (the proofs below
-- still unfold it through its equation lemmas with `simp only [mass]`)
attribute [local irreducible] mass

def main (inp : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  Circuit.forEach (Vector.finRange nSub) fun j =>
    assertZero (inp.subPrev[j] * (inp.subPrev[j] - 1))
  assertZero ((Fin.foldl nSub (fun acc j => acc + inp.subPrev[j]) 0) - 1)
  let prods ← Circuit.map edges fun e =>
    Mul.circuit { a := inp.subPrev[e.src], b := clsExpr inp.cls e.cls }
  Circuit.forEach (Vector.finRange nSub) fun j => do
    let gated ← Mul.circuit { a := inp.inStr, b := mass prods j.val }
    let new := if j.val = 0 then gated + (1 - inp.inStr) else gated
    let d ← Mul.circuit { a := inp.active, b := new - inp.subPrev[j] }
    assertZero (inp.subNext[j] - inp.subPrev[j] - d)

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

/-- The value-level twin of `clsExpr`. -/
def clsVal (c : ByteClass.Outputs (F circomPrime)) : SCls → F circomPrime
  | .quote => c.bytes.isQuote | .unescaped => c.classes.isUnescaped
  | .backslash => c.bytes.isBackslash | .lead2 => c.classes.isLead2 | .e0 => c.bytes.isE0
  | .lead3 => c.classes.isLead3 | .ed => c.bytes.isED | .f0 => c.bytes.isF0
  | .lead4 => c.classes.isLead4 | .f4 => c.bytes.isF4 | .simpleEsc => c.classes.isSimpleEsc
  | .lowerU => c.bytes.isLowerU | .hex => c.classes.isHex | .cont => c.classes.isCont
  | .contA0BF => c.classes.isContA0BF | .cont809F => c.classes.isCont809F
  | .cont90BF => c.classes.isCont90BF | .cont808F => c.classes.isCont808F

/-- `Expression.eval` pushed through `clsExpr`. -/
lemma eval_clsExpr (env : Environment (F circomPrime))
    (cv : ByteClass.Outputs (Expression (F circomPrime))) (c : SCls) :
    Expression.eval env (clsExpr cv c) = clsVal (evalCls env cv) c := by
  cases c <;> rfl

/-- The value-level twin of `mass`: the sum of the edge products entering `j`. -/
def massVal (c : ByteClass.Outputs (F circomPrime)) (subPrev : Vector (F circomPrime) nSub)
    (j : ℕ) : F circomPrime :=
  Fin.foldl 23 (fun acc e =>
    if (edges[e]).dst.val = j then acc + subPrev[(edges[e]).src] * clsVal c (edges[e]).cls else acc) 0

/-- The rows: `subPrev` is a one-hot-shaped vector (boolean entries summing to
one) and each `subNext` entry is the gated transition mass, frozen when the
position is inactive. -/
def Spec (inp : Inputs (F circomPrime)) : Prop :=
  (∀ j : Fin nSub, IsBool inp.subPrev[j]) ∧
  (∑ j : Fin nSub, inp.subPrev[j]) = 1 ∧
  ∀ j : Fin nSub, inp.subNext[j] = inp.subPrev[j] +
    inp.active * (inp.inStr * massVal inp.cls inp.subPrev j.val
      + (if j.val = 0 then 1 - inp.inStr else 0) - inp.subPrev[j])

set_option linter.constructorNameAsVariable false in
theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨e_inStr, e_active, ⟨⟨b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus,
    b_isPlus, b_isDot, b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF,
    b_isLowerN, b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero, b_isE0,
    b_isED, b_isF0, b_isF4⟩, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex, c_isHex,
    c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3, c_isLead4,
    c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F⟩, e_subPrev, e_subNext⟩ := h_input
  have hsp : ∀ (i : ℕ) (h : i < nSub),
      Expression.eval env (input_var_subPrev[i]'h) = input_subPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_subPrev i h
    simpa [Vector.getElem_map] using this
  have hsn : ∀ (i : ℕ) (h : i < nSub),
      Expression.eval env (input_var_subNext[i]'h) = input_subNext[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_subNext i h
    simpa [Vector.getElem_map] using this
  obtain ⟨h_bool, h_sum, h_prod, h_row⟩ := h_holds
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, mul_one, mul_zero, add_zero, true_implies,
    Vector.getElem_mapIdx, Fin.getElem_fin,
    eval_clsExpr, evalCls, Expression.eval, hsp, hsn, e_inStr, e_active,
    b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus, b_isPlus, b_isDot,
    b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF, b_isLowerN,
    b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero, b_isE0,
    b_isED, b_isF0, b_isF4, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex, c_isHex,
    c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3,
    c_isLead4, c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F] at h_prod h_bool h_row
  simp only [mass, eval_foldl_ite, Vector.getElem_mapIdx, Fin.getElem_fin, Mul.circuit_output,
    Mul.circuit_localLength, mul_one, mul_zero, add_zero, apply_ite (Expression.eval env),
    Expression.eval, e_inStr, h_prod] at h_row
  simp only [Mul.circuit_channelsWithRequirements, true_or, and_true, massVal, mul_zero, add_zero,
    Fin.getElem_fin]
  refine ⟨⟨fun j => ?_, ?_, fun j => ?_⟩, ?_⟩
  · rw [IsBool.iff_mul_sub_one]
    exact h_bool j
  · rw [eval_foldl_sum] at h_sum
    simp only [hsp, sub_eq_zero] at h_sum
    rw [← h_sum]
  · obtain ⟨g1, g2, g3⟩ := h_row j
    rw [g1] at g2
    rw [g2] at g3
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, if_pos, circuit_norm, e_inStr] at g3 ⊢
      linear_combination g3
    · simp only [hj, if_neg, if_false] at g3 ⊢
      linear_combination g3
  · exact ⟨fun _ => trivial, fun _ => trivial⟩

set_option linter.constructorNameAsVariable false in
theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨e_inStr, e_active, ⟨⟨b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus,
    b_isPlus, b_isDot, b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF,
    b_isLowerN, b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero, b_isE0,
    b_isED, b_isF0, b_isF4⟩, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex, c_isHex,
    c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3, c_isLead4,
    c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F⟩, e_subPrev, e_subNext⟩ := h_input
  have hsp : ∀ (i : ℕ) (h : i < nSub),
      Expression.eval env.toEnvironment (input_var_subPrev[i]'h) = input_subPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_subPrev i h
    simpa [Vector.getElem_map] using this
  have hsn : ∀ (i : ℕ) (h : i < nSub),
      Expression.eval env.toEnvironment (input_var_subNext[i]'h) = input_subNext[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_subNext i h
    simpa [Vector.getElem_map] using this
  obtain ⟨s_bool, s_sum, s_row⟩ := h_spec
  simp only [circuit_norm, Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, mul_one, mul_zero, add_zero, true_implies,
    Vector.getElem_mapIdx, Fin.getElem_fin,
    eval_clsExpr, evalCls, Expression.eval, hsp, hsn, e_inStr, e_active,
    b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus, b_isPlus, b_isDot,
    b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF, b_isLowerN,
    b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero, b_isE0,
    b_isED, b_isF0, b_isF4, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex, c_isHex,
    c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3,
    c_isLead4, c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F] at h_env ⊢
  obtain ⟨he_prod, he_row⟩ := h_env
  rw [Nat.add_comm 23 i₀] at he_row
  simp only [circuit_norm, Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, mul_one, mul_zero, add_zero, true_implies,
    Vector.getElem_mapIdx, Fin.getElem_fin, mass, eval_foldl_ite,
    apply_ite (Expression.eval env.toEnvironment),
    Expression.eval, hsp, hsn, e_inStr, e_active, he_prod] at he_row
  refine ⟨fun j => ?_, ?_, fun j => ?_⟩
  · rcases s_bool j with h | h <;> rw [h] <;> ring
  · rw [eval_foldl_sum]
    simp only [hsp]
    rw [s_sum]
    ring
  · obtain ⟨g1, g2⟩ := he_row j
    have hs := s_row j
    simp only [massVal, Fin.getElem_fin] at hs
    rw [g1] at g2
    rw [g2]
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, if_pos] at hs ⊢
      linear_combination hs
    · simp only [hj, if_neg, if_false] at hs ⊢
      linear_combination hs


def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end SubAutomaton
end Solution.JSONExtract
