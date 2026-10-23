import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circomlib.Bitify
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Mul
import Solution.JSONExtract.Model
import Solution.JSONExtract.ByteClassTheorems

/-!
# Byte classifier (`JSONExtract`)

A `FormalCircuit` computing, for one input byte, every class flag the
per-position automaton consumes (`Model.lean`): the single-byte tests by
`circomlib`'s `IsEqual`, the ranges from one 8-bit decomposition (`Num2Bits`)
as small products of bits, and the composite classes as affine combinations
of those. Every product is a witnessed single-multiplication row (`Mul`), so
all outputs are affine and the gadget is R1CS.

`Assumptions`: the input is a byte (`x.val < 256`). `Spec`: every flag is the
`0/1` indicator of the corresponding `Model` predicate on `x.val`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Circomlib

namespace ByteClass

/-- `2^8 < p`, for `Num2Bits 8`. -/
theorem two_pow_8_lt : 2 ^ 8 < circomPrime := by decide

/-- The single-byte tests. -/
structure Bytes (F : Type) where
  isLBrace : F
  isRBrace : F
  isQuote : F
  isColon : F
  isComma : F
  isMinus : F
  isPlus : F
  isDot : F
  isBackslash : F
  isSlash : F
  isLowerE : F
  isUpperE : F
  isLowerB : F
  isLowerF : F
  isLowerN : F
  isLowerR : F
  isLowerT : F
  isLowerU : F
  isLowerA : F
  isLowerL : F
  isLowerS : F
  isZero : F
  isE0 : F
  isED : F
  isF0 : F
  isF4 : F
deriving ProvableStruct

/-- The byte classes. -/
structure Classes (F : Type) where
  isWs : F
  isDigit : F
  isDigitNz : F
  isUpperHex : F
  isLowerHex : F
  isHex : F
  isUnescaped : F
  isSimpleEsc : F
  isExpLetter : F
  isSign : F
  isCont : F
  isLead2 : F
  isLead3 : F
  isLead4 : F
  isContA0BF : F
  isCont809F : F
  isCont90BF : F
  isCont808F : F
deriving ProvableStruct

/-- The class flags of one byte. -/
structure Outputs (F : Type) where
  bytes : Bytes F
  classes : Classes F
deriving ProvableStruct

/-- Witnessed product of two affine expressions. -/
def mul (a b : Expression (F circomPrime)) : Circuit (F circomPrime) (Expression (F circomPrime)) :=
  Mul.circuit { a := a, b := b }

def main (x : Var field (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  -- single-byte tests
  let eqLBrace ← IsEqual.circuit (x, 0x7B)
  let eqRBrace ← IsEqual.circuit (x, 0x7D)
  let eqQuote ← IsEqual.circuit (x, 0x22)
  let eqColon ← IsEqual.circuit (x, 0x3A)
  let eqComma ← IsEqual.circuit (x, 0x2C)
  let eqMinus ← IsEqual.circuit (x, 0x2D)
  let eqPlus ← IsEqual.circuit (x, 0x2B)
  let eqDot ← IsEqual.circuit (x, 0x2E)
  let eqBksl ← IsEqual.circuit (x, 0x5C)
  let eqSlash ← IsEqual.circuit (x, 0x2F)
  let eqLowerE ← IsEqual.circuit (x, 0x65)
  let eqUpperE ← IsEqual.circuit (x, 0x45)
  let eqLowerB ← IsEqual.circuit (x, 0x62)
  let eqLowerF ← IsEqual.circuit (x, 0x66)
  let eqLowerN ← IsEqual.circuit (x, 0x6E)
  let eqLowerR ← IsEqual.circuit (x, 0x72)
  let eqLowerT ← IsEqual.circuit (x, 0x74)
  let eqLowerU ← IsEqual.circuit (x, 0x75)
  let eqLowerA ← IsEqual.circuit (x, 0x61)
  let eqLowerL ← IsEqual.circuit (x, 0x6C)
  let eqLowerS ← IsEqual.circuit (x, 0x73)
  let eqZero ← IsEqual.circuit (x, 0x30)
  let eqE0 ← IsEqual.circuit (x, 0xE0)
  let eqED ← IsEqual.circuit (x, 0xED)
  let eqF0 ← IsEqual.circuit (x, 0xF0)
  let eqF4 ← IsEqual.circuit (x, 0xF4)
  let eqTab ← IsEqual.circuit (x, 0x09)
  let eqLf ← IsEqual.circuit (x, 0x0A)
  let eqCr ← IsEqual.circuit (x, 0x0D)
  let eqSpace ← IsEqual.circuit (x, 0x20)
  -- bits, least significant first
  let bits ← Num2Bits.circuit 8 two_pow_8_lt x
  let b0 := bits[0]
  let b1 := bits[1]
  let b2 := bits[2]
  let b3 := bits[3]
  let b4 := bits[4]
  let b5 := bits[5]
  let b6 := bits[6]
  let b7 := bits[7]
  -- high-nibble prefixes
  let n7n6 ← mul (1 - b7) (1 - b6)          -- 00xx xxxx
  let n7b6 ← mul (1 - b7) b6                -- 01xx xxxx
  let b7b6 ← mul b7 b6                      -- 11xx xxxx
  let hi0011 ← mul n7n6 b5 >>= fun t => mul t b4     -- 0011 xxxx
  let hi0100 ← mul n7b6 (1 - b5) >>= fun t => mul t (1 - b4)   -- 0100 xxxx
  let hi0110 ← mul n7b6 b5 >>= fun t => mul t (1 - b4)         -- 0110 xxxx
  let hi110 ← mul b7b6 (1 - b5)             -- 110x xxxx
  let hi1110 ← mul b7b6 b5 >>= fun t => mul t (1 - b4)         -- 1110 xxxx
  let hi1111 ← mul b7b6 b5 >>= fun t => mul t b4               -- 1111 xxxx
  -- low-nibble shapes
  let n2n1 ← mul (1 - b2) (1 - b1)
  let lowLe9 ← mul b3 n2n1 >>= fun t => pure ((1 - b3) + t)     -- xxxx ≤ 9
  let or21 ← mul b2 b1 >>= fun t => pure (b2 + b1 - t)          -- b2 ∨ b1
  let or210 ← mul or21 b0 >>= fun t => pure (or21 + b0 - t)     -- b2 ∨ b1 ∨ b0
  let and210 ← mul b2 b1 >>= fun t => mul t b0                  -- b2 ∧ b1 ∧ b0
  let low1to6 ← mul (1 - b3) or210 >>= fun t => mul t (1 - and210)  -- xxxx ∈ 1..6
  let lowLe1 ← mul n2n1 (1 - b3) >>= fun t => mul t (1 - b4)    -- xxx xxxx ∈ {0, 1} (bits 4..0)
  -- classes
  let isDigit ← mul hi0011 lowLe9
  let isUpperHex ← mul hi0100 low1to6
  let isLowerHex ← mul hi0110 low1to6
  let or65 ← mul b6 b5 >>= fun t => pure (b6 + b5 - t)
  let printable ← mul (1 - b7) or65                             -- 0x20..0x7F
  let isUnescaped ← mul printable (1 - eqQuote) >>= fun t => mul t (1 - eqBksl)
  let isCont ← mul b7 (1 - b6)                                  -- 10xx xxxx
  let isContA0BF ← mul isCont b5
  let isCont809F ← mul isCont (1 - b5)
  let or54 ← mul b5 b4 >>= fun t => pure (b5 + b4 - t)
  let isCont90BF ← mul isCont or54
  let isCont808F ← mul isCont809F (1 - b4)
  let isLead2 ← mul hi110 (1 - lowLe1)                          -- C2..DF (110x xxxx minus C0, C1)
  let isLead3 := hi1110 - eqE0 - eqED                           -- E1..EC, EE..EF
  let hi111100 ← mul hi1111 (1 - b3) >>= fun t => mul t (1 - b2)    -- 1111 00xx
  let isLead4 := hi111100 - eqF0                                -- F1..F3
  return {
    bytes := {
      isLBrace := eqLBrace, isRBrace := eqRBrace, isQuote := eqQuote, isColon := eqColon,
      isComma := eqComma, isMinus := eqMinus, isPlus := eqPlus, isDot := eqDot,
      isBackslash := eqBksl, isSlash := eqSlash, isLowerE := eqLowerE, isUpperE := eqUpperE,
      isLowerB := eqLowerB, isLowerF := eqLowerF, isLowerN := eqLowerN, isLowerR := eqLowerR,
      isLowerT := eqLowerT, isLowerU := eqLowerU, isLowerA := eqLowerA, isLowerL := eqLowerL,
      isLowerS := eqLowerS, isZero := eqZero, isE0 := eqE0, isED := eqED, isF0 := eqF0, isF4 := eqF4 }
    classes := {
    isWs := eqTab + eqLf + eqCr + eqSpace,
    isDigit := isDigit, isDigitNz := isDigit - eqZero,
    isUpperHex := isUpperHex, isLowerHex := isLowerHex,
    isHex := isDigit + isUpperHex + isLowerHex,
    isUnescaped := isUnescaped,
    isSimpleEsc := eqQuote + eqBksl + eqSlash + eqLowerB + eqLowerF + eqLowerN + eqLowerR + eqLowerT,
    isExpLetter := eqLowerE + eqUpperE, isSign := eqPlus + eqMinus,
    isCont := isCont, isLead2 := isLead2, isLead3 := isLead3, isLead4 := isLead4,
    isContA0BF := isContA0BF, isCont809F := isCont809F, isCont90BF := isCont90BF,
    isCont808F := isCont808F } }

set_option maxHeartbeats 2000000 in
instance elaborated : ElaboratedCircuit (F circomPrime) field Outputs main := by
  elaborate_circuit

def Assumptions (x : F circomPrime) : Prop := x.val < 256

/-- Every flag is the indicator of its `Model` predicate on the byte value. -/
def Spec (x : F circomPrime) (o : Outputs (F circomPrime)) : Prop :=
  let b := x.val
  o.bytes.isLBrace = ind (b == 0x7B) ∧ o.bytes.isRBrace = ind (b == 0x7D) ∧ o.bytes.isQuote = ind (b == 0x22) ∧
  o.bytes.isColon = ind (b == 0x3A) ∧ o.bytes.isComma = ind (b == 0x2C) ∧ o.bytes.isMinus = ind (b == 0x2D) ∧
  o.bytes.isPlus = ind (b == 0x2B) ∧ o.bytes.isDot = ind (b == 0x2E) ∧ o.bytes.isBackslash = ind (b == 0x5C) ∧
  o.bytes.isSlash = ind (b == 0x2F) ∧ o.bytes.isLowerE = ind (b == 0x65) ∧ o.bytes.isUpperE = ind (b == 0x45) ∧
  o.bytes.isLowerB = ind (b == 0x62) ∧ o.bytes.isLowerF = ind (b == 0x66) ∧ o.bytes.isLowerN = ind (b == 0x6E) ∧
  o.bytes.isLowerR = ind (b == 0x72) ∧ o.bytes.isLowerT = ind (b == 0x74) ∧ o.bytes.isLowerU = ind (b == 0x75) ∧
  o.bytes.isLowerA = ind (b == 0x61) ∧ o.bytes.isLowerL = ind (b == 0x6C) ∧ o.bytes.isLowerS = ind (b == 0x73) ∧
  o.bytes.isZero = ind (b == 0x30) ∧ o.bytes.isE0 = ind (b == 0xE0) ∧ o.bytes.isED = ind (b == 0xED) ∧
  o.bytes.isF0 = ind (b == 0xF0) ∧ o.bytes.isF4 = ind (b == 0xF4) ∧
  o.classes.isWs = ind (Model.isWs b) ∧ o.classes.isDigit = ind (Model.isDigit b) ∧
  o.classes.isDigitNz = ind (Model.isDigitNz b) ∧ o.classes.isUpperHex = ind (Model.isUpperHex b) ∧
  o.classes.isLowerHex = ind (Model.isLowerHex b) ∧ o.classes.isHex = ind (Model.isHex b) ∧
  o.classes.isUnescaped = ind (Model.isUnescaped b) ∧ o.classes.isSimpleEsc = ind (Model.isSimpleEsc b) ∧
  o.classes.isExpLetter = ind (Model.isExpLetter b) ∧ o.classes.isSign = ind (Model.isSign b) ∧
  o.classes.isCont = ind (Model.isCont b) ∧ o.classes.isLead2 = ind (Model.isLead2 b) ∧
  o.classes.isLead3 = ind (Model.isLead3 b) ∧ o.classes.isLead4 = ind (Model.isLead4 b) ∧
  o.classes.isContA0BF = ind (Model.isContA0BF b) ∧ o.classes.isCont809F = ind (Model.isCont809F b) ∧
  o.classes.isCont90BF = ind (Model.isCont90BF b) ∧ o.classes.isCont808F = ind (Model.isCont808F b)

set_option linter.constructorNameAsVariable false in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, mul, Mul.circuit_localLength, Mul.circuit_output,
    isEqual_localLength, isEqual_output, num2Bits_localLength, num2Bits_output]
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, isEqual_Assumptions, isEqual_Spec,
    num2Bits_Assumptions, num2Bits_Spec, true_implies,
    ind_eq_123, ind_eq_125, ind_eq_34, ind_eq_58, ind_eq_44, ind_eq_45, ind_eq_43, ind_eq_46,
    ind_eq_92, ind_eq_47, ind_eq_101, ind_eq_69, ind_eq_98, ind_eq_102, ind_eq_110, ind_eq_114,
    ind_eq_116, ind_eq_117, ind_eq_97, ind_eq_108, ind_eq_115, ind_eq_48, ind_eq_224,
    ind_eq_237, ind_eq_240, ind_eq_244, ind_eq_9, ind_eq_10, ind_eq_13, ind_eq_32] at h_holds
  obtain ⟨q123, q125, q34, q58, q44, q45, q43, q46, q92, q47, q101, q69, q98, q102, q110, q114,
    q116, q117, q97, q108, q115, q48, q224, q237, q240, q244, q9, q10, q13, q32, hn2b, m1, m2, m3,
    m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23,
    m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38⟩ := h_holds
  obtain ⟨-, hbits⟩ := hn2b
  rw [Vector.ext_iff] at hbits
  simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval, fieldToBits_ind] at hbits
  simp only [Mul.circuit_channelsWithRequirements, isEqual_channelsWithRequirements,
    num2Bits_channelsWithRequirements, true_or, and_true, and_self,
    hbits 0 (by norm_num), hbits 1 (by norm_num), hbits 2 (by norm_num), hbits 3 (by norm_num), hbits 4 (by norm_num), hbits 5 (by norm_num), hbits 6 (by norm_num), hbits 7 (by norm_num),
    m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38,
    q123, q125, q34, q58, q44, q45, q43, q46, q92, q47, q101, q69, q98, q102, q110, q114, q116,
    q117, q97, q108, q115, q48, q224, q237, q240, q244, q9, q10, q13, q32]
  -- 4.33: `Expression.eval_sub` is `circuit_norm`, so the affine combinations arrive
  -- spelled with `-`; the `ByteClassTheorems` bridges are stated with `+ -`
  simp only [sub_eq_add_neg]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, trivial, trivial, trivial, trivial, ws_ind _ h_assumptions, digit_ind _
    h_assumptions, digitNz_ind _ h_assumptions, ?_, ?_, ?_, unescaped_ind _ h_assumptions,
    simpleEsc_ind _ h_assumptions, expLetter_ind _ h_assumptions, sign_ind _ h_assumptions, cont_ind
    _ h_assumptions, ?_, lead3_ind _ h_assumptions, ?_, contA0BF_ind _ h_assumptions, cont809F_ind _
    h_assumptions, cont90BF_ind _ h_assumptions, cont808F_ind _ h_assumptions⟩
  · simp only [one_add_neg_ind, ind_mul, ind_add_sub_and]
    exact congrArg ind (bridge_upperHex ⟨_, h_assumptions⟩)
  · simp only [one_add_neg_ind, ind_mul, ind_add_sub_and]
    exact congrArg ind (bridge_lowerHex ⟨_, h_assumptions⟩)
  · simp only [one_add_neg_ind, ind_mul, ind_add_not, ind_add_sub_and]
    rw [ind_add_disj (bridge_hex_disjDU ⟨_, h_assumptions⟩),
      ind_add_disj (bridge_hex_disjL ⟨_, h_assumptions⟩)]
    exact congrArg ind (bridge_hex ⟨_, h_assumptions⟩)
  · simp only [one_add_neg_ind, ind_mul]
    exact congrArg ind (bridge_lead2 ⟨_, h_assumptions⟩)
  · simp only [one_add_neg_ind, ind_mul]
    rw [ind_add_neg (bridge_lead4_disjF0 ⟨_, h_assumptions⟩)]
    exact congrArg ind (bridge_lead4 ⟨_, h_assumptions⟩)

set_option linter.constructorNameAsVariable false in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [Assumptions, mul, Mul.circuit_localLength, Mul.circuit_output,
    isEqual_localLength, isEqual_output, num2Bits_localLength, num2Bits_output]
  simp only [Mul.circuit_Assumptions, isEqual_Assumptions, num2Bits_ProverAssumptions,
    true_and, and_true, and_self]
  simpa using h_assumptions

def circuit : FormalCircuit (F circomPrime) field Outputs where
  main; elaborated; Assumptions; Spec; soundness; completeness
  -- the default tactic normalizes the unfolded `main` with `circuit_norm`, which is
  -- hopeless for a gadget with this many subcircuits; see `Theorems.lean`
  requirementsChannelsLawful := fun _ _ =>
    requirementsChannelsLawful_of_noChannels rfl rfl

end ByteClass
end Solution.JSONExtract
