import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Mul
import Solution.JSONExtract.Model
import Solution.JSONExtract.ByteClass
import Solution.JSONExtract.AutomatonTheorems

/-!
# The main automaton, one position (`JSONExtract`)

A `FormalAssertion` relating the main state before a byte to the witnessed
state after it (`Model.stepSt`): the next state is the successor of the edge
the byte takes, where the edges out of `PVAL` and into the fraction/exponent
states are additionally gated by the kind of the value being read (a known
claim's value must have the claim's type); no edge means no satisfying
successor and the byte is rejected; at an inactive position the state is
frozen.

Inputs: the activity flag, the materialized `closeQuote = isQuote · subPlain`
(a `"` closes a string only when the sub-automaton is in `PLAIN`), the byte
classes, the kind flags `(str, int, bool, unk)` of the claim register, and the
two states.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSt St)

namespace MainAutomaton

structure Inputs (F : Type) where
  active : F
  closeQuote : F
  cls : ByteClass.Outputs F
  /-- `(str, int, bool, unk)` -/
  kinds : Vector F 4
  stPrev : Vector F nSt
  stNext : Vector F nSt
deriving ProvableStruct

/-- Byte classes an edge can read. -/
inductive Cls where
  | ws | lbrace | rbrace | quote | closeQuote | notCloseQuote | colon | comma | minus
  | zero | digitNz | digit | dot | expLetter | sign
  | lowerT | lowerR | lowerU | lowerE | lowerF | lowerA | lowerL | lowerS | lowerN
deriving DecidableEq, Repr, Inhabited

/-- Type gates of the value being read. -/
inductive Gate where
  | strOrUnk | intOrUnk | boolOrUnk | unk
deriving DecidableEq, Repr, Inhabited

structure Edge where
  src : St
  cls : Cls
  dst : St
deriving Repr, Inhabited

structure GatedEdge where
  src : St
  cls : Cls
  dst : St
  gate : Gate
deriving Repr, Inhabited

open Model.St in
/-- The ungated edges (mirrors `Model.stepSt`). -/
def plainEdges : Vector Edge 50 := #v[
  ⟨PRE, .ws, PRE⟩, ⟨PRE, .lbrace, OBJ⟩,
  ⟨OBJ, .ws, OBJ⟩, ⟨OBJ, .quote, KEY⟩, ⟨OBJ, .rbrace, END⟩,
  ⟨KEY, .closeQuote, AKEY⟩, ⟨KEY, .notCloseQuote, KEY⟩,
  ⟨AKEY, .ws, AKEY⟩, ⟨AKEY, .colon, PVAL⟩,
  ⟨PVAL, .ws, PVAL⟩,
  ⟨STR, .closeQuote, AVAL⟩, ⟨STR, .notCloseQuote, STR⟩,
  ⟨NSIGN, .zero, NZERO⟩, ⟨NSIGN, .digitNz, NINT⟩,
  ⟨NZERO, .ws, AVAL⟩, ⟨NZERO, .comma, SEP⟩, ⟨NZERO, .rbrace, END⟩,
  ⟨NINT, .digit, NINT⟩, ⟨NINT, .ws, AVAL⟩, ⟨NINT, .comma, SEP⟩, ⟨NINT, .rbrace, END⟩,
  ⟨NDOT, .digit, NFRAC⟩,
  ⟨NFRAC, .digit, NFRAC⟩, ⟨NFRAC, .expLetter, NE⟩, ⟨NFRAC, .ws, AVAL⟩, ⟨NFRAC, .comma, SEP⟩,
  ⟨NFRAC, .rbrace, END⟩,
  ⟨NE, .sign, NESIGN⟩, ⟨NE, .digit, NEXP⟩,
  ⟨NESIGN, .digit, NEXP⟩,
  ⟨NEXP, .digit, NEXP⟩, ⟨NEXP, .ws, AVAL⟩, ⟨NEXP, .comma, SEP⟩, ⟨NEXP, .rbrace, END⟩,
  ⟨T1, .lowerR, T2⟩, ⟨T2, .lowerU, T3⟩, ⟨T3, .lowerE, AVAL⟩,
  ⟨F1, .lowerA, F2⟩, ⟨F2, .lowerL, F3⟩, ⟨F3, .lowerS, F4⟩, ⟨F4, .lowerE, AVAL⟩,
  ⟨N1, .lowerU, N2⟩, ⟨N2, .lowerL, N3⟩, ⟨N3, .lowerL, AVAL⟩,
  ⟨AVAL, .ws, AVAL⟩, ⟨AVAL, .comma, SEP⟩, ⟨AVAL, .rbrace, END⟩,
  ⟨SEP, .ws, SEP⟩, ⟨SEP, .quote, KEY⟩,
  ⟨END, .ws, END⟩]

open Model.St in
/-- The type-gated edges. -/
def gatedEdges : Vector GatedEdge 11 := #v[
  ⟨PVAL, .quote, STR, .strOrUnk⟩,
  ⟨PVAL, .minus, NSIGN, .intOrUnk⟩, ⟨PVAL, .zero, NZERO, .intOrUnk⟩,
  ⟨PVAL, .digitNz, NINT, .intOrUnk⟩,
  ⟨PVAL, .lowerT, T1, .boolOrUnk⟩, ⟨PVAL, .lowerF, F1, .boolOrUnk⟩,
  ⟨PVAL, .lowerN, N1, .unk⟩,
  ⟨NZERO, .dot, NDOT, .unk⟩, ⟨NZERO, .expLetter, NE, .unk⟩,
  ⟨NINT, .dot, NDOT, .unk⟩, ⟨NINT, .expLetter, NE, .unk⟩]

abbrev E := Expression (F circomPrime)

def clsExpr (c : ByteClass.Outputs E) (closeQuote : E) : Cls → E
  | .ws => c.classes.isWs | .lbrace => c.bytes.isLBrace | .rbrace => c.bytes.isRBrace
  | .quote => c.bytes.isQuote | .closeQuote => closeQuote | .notCloseQuote => 1 - closeQuote
  | .colon => c.bytes.isColon | .comma => c.bytes.isComma | .minus => c.bytes.isMinus
  | .zero => c.bytes.isZero | .digitNz => c.classes.isDigitNz | .digit => c.classes.isDigit
  | .dot => c.bytes.isDot | .expLetter => c.classes.isExpLetter | .sign => c.classes.isSign
  | .lowerT => c.bytes.isLowerT | .lowerR => c.bytes.isLowerR | .lowerU => c.bytes.isLowerU
  | .lowerE => c.bytes.isLowerE | .lowerF => c.bytes.isLowerF | .lowerA => c.bytes.isLowerA
  | .lowerL => c.bytes.isLowerL | .lowerS => c.bytes.isLowerS | .lowerN => c.bytes.isLowerN

def gateExpr (k : Vector E 4) : Gate → E
  | .strOrUnk => k[0] + k[3] | .intOrUnk => k[1] + k[3]
  | .boolOrUnk => k[2] + k[3] | .unk => k[3]

/-- The sum of the ungated edge products entering state `j`. -/
def plainMass (prods : Vector E 50) (j : ℕ) : E :=
  Fin.foldl 50 (fun acc e => if (plainEdges[e]).dst.val = j then acc + prods[e] else acc) 0

/-- The sum of the gated edge products entering state `j`. -/
def gatedMass (prods : Vector E 11) (j : ℕ) : E :=
  Fin.foldl 11 (fun acc e => if (gatedEdges[e]).dst.val = j then acc + prods[e] else acc) 0

-- 4.33: `circuit_norm` reduces concrete folds, so the constant-length side goals of
-- `Circuit.forEach` try to evaluate the 50- and 11-edge mass sums; seal them (the proofs
-- below still unfold them through their equation lemmas with `simp only [plainMass, ...]`)
attribute [local irreducible] plainMass gatedMass

def main (inp : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  Circuit.forEach (Vector.finRange nSt) fun j =>
    assertZero (inp.stPrev[j] * (inp.stPrev[j] - 1))
  assertZero ((Fin.foldl nSt (fun acc j => acc + inp.stPrev[j]) 0) - 1)
  let plainProds ← Circuit.map plainEdges fun e =>
    Mul.circuit { a := inp.stPrev[e.src], b := clsExpr inp.cls inp.closeQuote e.cls }
  let gatedProds ← Circuit.map gatedEdges fun e => do
    let p ← Mul.circuit { a := inp.stPrev[e.src], b := clsExpr inp.cls inp.closeQuote e.cls }
    Mul.circuit { a := p, b := gateExpr inp.kinds e.gate }
  Circuit.forEach (Vector.finRange nSt) fun j => do
    let d ← Mul.circuit
      { a := inp.active, b := plainMass plainProds j.val + gatedMass gatedProds j.val - inp.stPrev[j] }
    assertZero (inp.stNext[j] - inp.stPrev[j] - d)

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

/-- The value-level twin of `clsExpr`. -/
def clsVal (c : ByteClass.Outputs (F circomPrime)) (closeQuote : F circomPrime) :
    Cls → F circomPrime
  | .ws => c.classes.isWs | .lbrace => c.bytes.isLBrace | .rbrace => c.bytes.isRBrace
  | .quote => c.bytes.isQuote | .closeQuote => closeQuote | .notCloseQuote => 1 - closeQuote
  | .colon => c.bytes.isColon | .comma => c.bytes.isComma | .minus => c.bytes.isMinus
  | .zero => c.bytes.isZero | .digitNz => c.classes.isDigitNz | .digit => c.classes.isDigit
  | .dot => c.bytes.isDot | .expLetter => c.classes.isExpLetter | .sign => c.classes.isSign
  | .lowerT => c.bytes.isLowerT | .lowerR => c.bytes.isLowerR | .lowerU => c.bytes.isLowerU
  | .lowerE => c.bytes.isLowerE | .lowerF => c.bytes.isLowerF | .lowerA => c.bytes.isLowerA
  | .lowerL => c.bytes.isLowerL | .lowerS => c.bytes.isLowerS | .lowerN => c.bytes.isLowerN

/-- The value-level twin of `gateExpr`. -/
def gateVal (k : Vector (F circomPrime) 4) : Gate → F circomPrime
  | .strOrUnk => k[0] + k[3] | .intOrUnk => k[1] + k[3]
  | .boolOrUnk => k[2] + k[3] | .unk => k[3]

/-- `Expression.eval` pushed through `clsExpr`. -/
lemma eval_clsExpr (env : Environment (F circomPrime))
    (cv : ByteClass.Outputs (Expression (F circomPrime))) (cq : Expression (F circomPrime))
    (c : Cls) :
    Expression.eval env (clsExpr cv cq c) =
      clsVal (evalCls env cv) (Expression.eval env cq) c := by
  cases c <;> first | rfl | simp only [clsExpr, clsVal, circuit_norm]

/-- `Expression.eval` pushed through `gateExpr`. -/
lemma eval_gateExpr (env : Environment (F circomPrime))
    (kv : Vector (Expression (F circomPrime)) 4) (g : Gate) :
    Expression.eval env (gateExpr kv g) = gateVal (Vector.map (Expression.eval env) kv) g := by
  cases g <;> simp [gateExpr, gateVal, Expression.eval]

/-- The value-level twin of `plainMass`. -/
def plainMassVal (c : ByteClass.Outputs (F circomPrime)) (cq : F circomPrime)
    (stPrev : Vector (F circomPrime) nSt) (j : ℕ) : F circomPrime :=
  Fin.foldl 50 (fun acc e =>
    if (plainEdges[e]).dst.val = j then
      acc + stPrev[(plainEdges[e]).src] * clsVal c cq (plainEdges[e]).cls
    else acc) 0

/-- The value-level twin of `gatedMass`. -/
def gatedMassVal (c : ByteClass.Outputs (F circomPrime)) (cq : F circomPrime)
    (kinds : Vector (F circomPrime) 4) (stPrev : Vector (F circomPrime) nSt) (j : ℕ) :
    F circomPrime :=
  Fin.foldl 11 (fun acc e =>
    if (gatedEdges[e]).dst.val = j then
      acc + stPrev[(gatedEdges[e]).src] * clsVal c cq (gatedEdges[e]).cls *
        gateVal kinds (gatedEdges[e]).gate
    else acc) 0

/-- The rows: `stPrev` is a one-hot-shaped vector (boolean entries summing to
one) and each `stNext` entry is the transition mass, frozen when the position is
inactive. -/
def Spec (inp : Inputs (F circomPrime)) : Prop :=
  (∀ j : Fin nSt, IsBool inp.stPrev[j]) ∧
  (∑ j : Fin nSt, inp.stPrev[j]) = 1 ∧
  ∀ j : Fin nSt, inp.stNext[j] = inp.stPrev[j] +
    inp.active * (plainMassVal inp.cls inp.closeQuote inp.stPrev j.val
      + gatedMassVal inp.cls inp.closeQuote inp.kinds inp.stPrev j.val - inp.stPrev[j])

set_option linter.constructorNameAsVariable false in
theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨e_active, e_cq, ⟨⟨b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus,
    b_isPlus, b_isDot, b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF,
    b_isLowerN, b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero,
    b_isE0, b_isED, b_isF0, b_isF4⟩, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex,
    c_isHex, c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3,
    c_isLead4, c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F⟩, e_kinds, e_stPrev, e_stNext⟩ := h_input
  have hsp : ∀ (i : ℕ) (h : i < nSt),
      Expression.eval env (input_var_stPrev[i]'h) = input_stPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_stPrev i h
    simpa [Vector.getElem_map] using this
  have hsn : ∀ (i : ℕ) (h : i < nSt),
      Expression.eval env (input_var_stNext[i]'h) = input_stNext[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_stNext i h
    simpa [Vector.getElem_map] using this
  obtain ⟨h_bool, h_sum, h_plain, h_gated, h_row⟩ := h_holds
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, mul_one, mul_zero, add_zero, true_implies,
    Vector.getElem_mapIdx, Fin.getElem_fin,
    eval_clsExpr, eval_gateExpr, evalCls, Expression.eval, hsp, hsn, e_active, e_cq, e_kinds,
    b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus, b_isPlus, b_isDot,
    b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF, b_isLowerN,
    b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero, b_isE0,
    b_isED, b_isF0, b_isF4, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex, c_isHex,
    c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3,
    c_isLead4, c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F] at h_plain h_gated h_bool h_row
  have hg1 := fun i => (h_gated i).1
  have hg2 := fun i => (h_gated i).2
  simp only [plainMass, gatedMass, eval_foldl_ite, Vector.getElem_mapIdx, Fin.getElem_fin,
    Mul.circuit_output, Mul.circuit_localLength, mul_one, mul_zero, add_zero,
    Expression.eval, hg2, hg1, h_plain] at h_row
  simp only [Mul.circuit_channelsWithRequirements, true_or, and_true, and_self,
    plainMassVal, gatedMassVal, mul_zero, add_zero, Fin.getElem_fin]
  refine ⟨⟨fun j => ?_, ?_, fun j => ?_⟩, ?_⟩
  · rw [IsBool.iff_mul_sub_one]
    exact h_bool j
  · rw [eval_foldl_sum] at h_sum
    simp only [hsp, sub_eq_zero] at h_sum
    rw [← h_sum]
  · obtain ⟨g1, g2⟩ := h_row j
    rw [g1] at g2
    linear_combination g2
  · exact ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial⟩


set_option linter.constructorNameAsVariable false in
theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨e_active, e_cq, ⟨⟨b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus,
    b_isPlus, b_isDot, b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF,
    b_isLowerN, b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero,
    b_isE0, b_isED, b_isF0, b_isF4⟩, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex,
    c_isHex, c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3,
    c_isLead4, c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F⟩, e_kinds, e_stPrev, e_stNext⟩ := h_input
  have hsp : ∀ (i : ℕ) (h : i < nSt),
      Expression.eval env.toEnvironment (input_var_stPrev[i]'h) = input_stPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_stPrev i h
    simpa [Vector.getElem_map] using this
  have hsn : ∀ (i : ℕ) (h : i < nSt),
      Expression.eval env.toEnvironment (input_var_stNext[i]'h) = input_stNext[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_stNext i h
    simpa [Vector.getElem_map] using this
  obtain ⟨s_bool, s_sum, s_row⟩ := h_spec
  simp only [circuit_norm, Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, mul_one, mul_zero, add_zero, true_implies,
    Vector.getElem_mapIdx, Fin.getElem_fin,
    eval_clsExpr, eval_gateExpr, evalCls, Expression.eval, hsp, hsn, e_active, e_cq, e_kinds,
    b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus, b_isPlus, b_isDot,
    b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF, b_isLowerN,
    b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero, b_isE0,
    b_isED, b_isF0, b_isF4, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex, c_isHex,
    c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3,
    c_isLead4, c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F] at h_env ⊢
  simp only [Nat.add_comm 50 i₀] at h_env
  simp only [circuit_norm, Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, mul_one, mul_zero, add_zero, true_implies,
    Vector.getElem_mapIdx, Fin.getElem_fin,
    eval_clsExpr, eval_gateExpr, evalCls, Expression.eval, hsp, hsn, e_active, e_cq, e_kinds,
    b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus, b_isPlus, b_isDot,
    b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF, b_isLowerN,
    b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero, b_isE0,
    b_isED, b_isF0, b_isF4, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex, c_isHex,
    c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3,
    c_isLead4, c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F] at h_env
  simp only [Nat.add_comm (11 * 2) (i₀ + 50)] at h_env
  simp only [circuit_norm, Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_output,
    Mul.circuit_localLength, mul_one, mul_zero, add_zero, true_implies,
    Vector.getElem_mapIdx, Fin.getElem_fin,
    eval_clsExpr, eval_gateExpr, evalCls, Expression.eval, hsp, hsn, e_active, e_cq, e_kinds,
    b_isLBrace, b_isRBrace, b_isQuote, b_isColon, b_isComma, b_isMinus, b_isPlus, b_isDot,
    b_isBackslash, b_isSlash, b_isLowerE, b_isUpperE, b_isLowerB, b_isLowerF, b_isLowerN,
    b_isLowerR, b_isLowerT, b_isLowerU, b_isLowerA, b_isLowerL, b_isLowerS, b_isZero, b_isE0,
    b_isED, b_isF0, b_isF4, c_isWs, c_isDigit, c_isDigitNz, c_isUpperHex, c_isLowerHex, c_isHex,
    c_isUnescaped, c_isSimpleEsc, c_isExpLetter, c_isSign, c_isCont, c_isLead2, c_isLead3,
    c_isLead4, c_isContA0BF, c_isCont809F, c_isCont90BF, c_isCont808F, plainMass, gatedMass, eval_foldl_ite,
    Mul.circuit_output, Mul.circuit_localLength] at h_env
  obtain ⟨he_plain, he_gated, he_row⟩ := h_env
  have hg1 := fun i => (he_gated i).1
  have hg2 := fun i => (he_gated i).2
  simp only [hg2, hg1, he_plain] at he_row
  refine ⟨fun j => ?_, ?_, fun j => ?_⟩
  · rcases s_bool j with h | h <;> rw [h] <;> ring
  · rw [eval_foldl_sum]
    simp only [hsp]
    rw [s_sum]
    ring
  · have hs := s_row j
    simp only [plainMassVal, gatedMassVal, Fin.getElem_fin] at hs
    rw [he_row j]
    linear_combination hs


def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end MainAutomaton
end Solution.JSONExtract
