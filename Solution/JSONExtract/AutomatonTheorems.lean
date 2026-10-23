import Solution.JSONExtract.ByteClass
import Solution.JSONExtract.Theorems

/-!
# Shared helper for the two per-position automaton assertions

`SubAutomaton` and `MainAutomaton` both read the byte classifier's output
struct through their own `clsExpr`; this is the fieldwise `Expression.eval` of
that struct, the value both `eval_clsExpr` lemmas are stated against.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

/-- `Expression.eval` applied fieldwise to a `ByteClass.Outputs` of expressions. -/
def evalCls (env : Environment (F circomPrime))
    (cv : ByteClass.Outputs (Expression (F circomPrime))) : ByteClass.Outputs (F circomPrime) where
  bytes :=
    { isLBrace := Expression.eval env cv.bytes.isLBrace,
      isRBrace := Expression.eval env cv.bytes.isRBrace,
      isQuote := Expression.eval env cv.bytes.isQuote,
      isColon := Expression.eval env cv.bytes.isColon,
      isComma := Expression.eval env cv.bytes.isComma,
      isMinus := Expression.eval env cv.bytes.isMinus,
      isPlus := Expression.eval env cv.bytes.isPlus,
      isDot := Expression.eval env cv.bytes.isDot,
      isBackslash := Expression.eval env cv.bytes.isBackslash,
      isSlash := Expression.eval env cv.bytes.isSlash,
      isLowerE := Expression.eval env cv.bytes.isLowerE,
      isUpperE := Expression.eval env cv.bytes.isUpperE,
      isLowerB := Expression.eval env cv.bytes.isLowerB,
      isLowerF := Expression.eval env cv.bytes.isLowerF,
      isLowerN := Expression.eval env cv.bytes.isLowerN,
      isLowerR := Expression.eval env cv.bytes.isLowerR,
      isLowerT := Expression.eval env cv.bytes.isLowerT,
      isLowerU := Expression.eval env cv.bytes.isLowerU,
      isLowerA := Expression.eval env cv.bytes.isLowerA,
      isLowerL := Expression.eval env cv.bytes.isLowerL,
      isLowerS := Expression.eval env cv.bytes.isLowerS,
      isZero := Expression.eval env cv.bytes.isZero,
      isE0 := Expression.eval env cv.bytes.isE0,
      isED := Expression.eval env cv.bytes.isED,
      isF0 := Expression.eval env cv.bytes.isF0,
      isF4 := Expression.eval env cv.bytes.isF4 }
  classes :=
    { isWs := Expression.eval env cv.classes.isWs,
      isDigit := Expression.eval env cv.classes.isDigit,
      isDigitNz := Expression.eval env cv.classes.isDigitNz,
      isUpperHex := Expression.eval env cv.classes.isUpperHex,
      isLowerHex := Expression.eval env cv.classes.isLowerHex,
      isHex := Expression.eval env cv.classes.isHex,
      isUnescaped := Expression.eval env cv.classes.isUnescaped,
      isSimpleEsc := Expression.eval env cv.classes.isSimpleEsc,
      isExpLetter := Expression.eval env cv.classes.isExpLetter,
      isSign := Expression.eval env cv.classes.isSign,
      isCont := Expression.eval env cv.classes.isCont,
      isLead2 := Expression.eval env cv.classes.isLead2,
      isLead3 := Expression.eval env cv.classes.isLead3,
      isLead4 := Expression.eval env cv.classes.isLead4,
      isContA0BF := Expression.eval env cv.classes.isContA0BF,
      isCont809F := Expression.eval env cv.classes.isCont809F,
      isCont90BF := Expression.eval env cv.classes.isCont90BF,
      isCont808F := Expression.eval env cv.classes.isCont808F }


open ByteClass (ind)
open Model (Claim)

/-! ## The byte classes as a function of the byte -/

/-- The classifier's output as a function of the byte value: every flag is the
`0/1` indicator of its `Model` predicate.  This is exactly what
`ByteClass.Spec` says about the flags the gadget returns
(`byteClass_spec_iff`). -/
def classesOf (b : ℕ) : ByteClass.Outputs (F circomPrime) where
  bytes :=
    { isLBrace := ind (b == 0x7B), isRBrace := ind (b == 0x7D), isQuote := ind (b == 0x22),
      isColon := ind (b == 0x3A), isComma := ind (b == 0x2C), isMinus := ind (b == 0x2D),
      isPlus := ind (b == 0x2B), isDot := ind (b == 0x2E), isBackslash := ind (b == 0x5C),
      isSlash := ind (b == 0x2F), isLowerE := ind (b == 0x65), isUpperE := ind (b == 0x45),
      isLowerB := ind (b == 0x62), isLowerF := ind (b == 0x66), isLowerN := ind (b == 0x6E),
      isLowerR := ind (b == 0x72), isLowerT := ind (b == 0x74), isLowerU := ind (b == 0x75),
      isLowerA := ind (b == 0x61), isLowerL := ind (b == 0x6C), isLowerS := ind (b == 0x73),
      isZero := ind (b == 0x30), isE0 := ind (b == 0xE0), isED := ind (b == 0xED),
      isF0 := ind (b == 0xF0), isF4 := ind (b == 0xF4) }
  classes :=
    { isWs := ind (Model.isWs b), isDigit := ind (Model.isDigit b),
      isDigitNz := ind (Model.isDigitNz b), isUpperHex := ind (Model.isUpperHex b),
      isLowerHex := ind (Model.isLowerHex b), isHex := ind (Model.isHex b),
      isUnescaped := ind (Model.isUnescaped b), isSimpleEsc := ind (Model.isSimpleEsc b),
      isExpLetter := ind (Model.isExpLetter b), isSign := ind (Model.isSign b),
      isCont := ind (Model.isCont b), isLead2 := ind (Model.isLead2 b),
      isLead3 := ind (Model.isLead3 b), isLead4 := ind (Model.isLead4 b),
      isContA0BF := ind (Model.isContA0BF b), isCont809F := ind (Model.isCont809F b),
      isCont90BF := ind (Model.isCont90BF b), isCont808F := ind (Model.isCont808F b) }


end Solution.JSONExtract
