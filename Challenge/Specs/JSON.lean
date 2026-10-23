import Mathlib.Data.Nat.Log
import Challenge.Specs.Parser

/-!
# A pure Lean specification of a JSON parser (RFC 8259 / ECMA-404)

This file specifies a JSON parser as a pure function

```
parse : Vector ℕ n → Option JSON
```

taking a vector of natural numbers (interpreted as bytes) and returning
`some value` when the whole input is a single well-formed JSON document, and
`none` otherwise.

The grammar is written with the parser combinators of `Specs.Parser`, in two
stages, both over `List ℕ`:

1. `utf8Decode`: the byte stream is decoded into Unicode code points by the
   grammar `codepoint` (any invalid, overlong, surrogate or out-of-range
   sequence is rejected).
2. `document`: the code-point list is parsed according to the JSON grammar
   (`ws`, `string` with escapes, `number`, `value`, `array`, `object`). Nested
   values recurse on a fuel argument that bounds the nesting depth; every
   nesting level consumes at least one code point, so `cps.length + 1` fuel
   always suffices.

Every byte and code point the grammar mentions is a named constant below.
-/

set_option linter.dupNamespace false

namespace Specs.JSON

open Specs.Parser

/-- A JSON number stored structurally so that no digit is lost and equality is
    exact. It denotes `-?(0|[1-9][0-9]*)(\.frac)?([eE][+-]?exp)?`. -/
structure JNumber where
  /-- whether the number carries a leading `-`. -/
  negative : Bool
  /-- decimal digits of the integer part (digit *values* 0–9); `[0]` for `0`. -/
  intDigits : List Nat
  /-- digits after the `.`; empty when there is no fractional part. -/
  fracDigits : List Nat
  /-- whether the exponent carries a `-` (a `+` or absent sign gives `false`). -/
  expNegative : Bool
  /-- exponent digits; empty when there is no exponent at all. -/
  expDigits : List Nat
deriving DecidableEq, Repr, Inhabited

/-- A structured JSON value. Strings and object keys are decoded to lists of
    Unicode code points; object members keep their source order. -/
inductive JSON where
  | null
  | bool (b : Bool)
  | num (n : JNumber)
  | str (s : List Nat)
  | arr (elems : List JSON)
  | obj (members : List (List Nat × JSON))
deriving Repr, Inhabited

/-! ### Decidable equality

    Lean's `deriving DecidableEq` handler does not support inductives that recurse
    through `List` (as `arr`/`obj` do), so we build the instance by hand with a
    mutual structural recursion. -/

mutual

/-- Decidable equality on `JSON` values. -/
def JSON.deq : (a b : JSON) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool x, .bool y =>
      if h : x = y then isTrue (by rw [h]) else isFalse (by intro he; injection he; contradiction)
  | .num x, .num y =>
      if h : x = y then isTrue (by rw [h]) else isFalse (by intro he; injection he; contradiction)
  | .str x, .str y =>
      if h : x = y then isTrue (by rw [h]) else isFalse (by intro he; injection he; contradiction)
  | .arr x, .arr y =>
      match JSON.deqList x y with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro he; injection he; contradiction)
  | .obj x, .obj y =>
      match JSON.deqMembers x y with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro he; injection he; contradiction)
  | .null, .bool _ => isFalse (by intro h; cases h)
  | .null, .num _ => isFalse (by intro h; cases h)
  | .null, .str _ => isFalse (by intro h; cases h)
  | .null, .arr _ => isFalse (by intro h; cases h)
  | .null, .obj _ => isFalse (by intro h; cases h)
  | .bool _, .null => isFalse (by intro h; cases h)
  | .bool _, .num _ => isFalse (by intro h; cases h)
  | .bool _, .str _ => isFalse (by intro h; cases h)
  | .bool _, .arr _ => isFalse (by intro h; cases h)
  | .bool _, .obj _ => isFalse (by intro h; cases h)
  | .num _, .null => isFalse (by intro h; cases h)
  | .num _, .bool _ => isFalse (by intro h; cases h)
  | .num _, .str _ => isFalse (by intro h; cases h)
  | .num _, .arr _ => isFalse (by intro h; cases h)
  | .num _, .obj _ => isFalse (by intro h; cases h)
  | .str _, .null => isFalse (by intro h; cases h)
  | .str _, .bool _ => isFalse (by intro h; cases h)
  | .str _, .num _ => isFalse (by intro h; cases h)
  | .str _, .arr _ => isFalse (by intro h; cases h)
  | .str _, .obj _ => isFalse (by intro h; cases h)
  | .arr _, .null => isFalse (by intro h; cases h)
  | .arr _, .bool _ => isFalse (by intro h; cases h)
  | .arr _, .num _ => isFalse (by intro h; cases h)
  | .arr _, .str _ => isFalse (by intro h; cases h)
  | .arr _, .obj _ => isFalse (by intro h; cases h)
  | .obj _, .null => isFalse (by intro h; cases h)
  | .obj _, .bool _ => isFalse (by intro h; cases h)
  | .obj _, .num _ => isFalse (by intro h; cases h)
  | .obj _, .str _ => isFalse (by intro h; cases h)
  | .obj _, .arr _ => isFalse (by intro h; cases h)

/-- Decidable equality on lists of `JSON` values. -/
def JSON.deqList : (a b : List JSON) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | a :: as, b :: bs =>
      match JSON.deq a b, JSON.deqList as bs with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h1, _ => isFalse (by intro he; injection he; contradiction)
      | _, isFalse h2 => isFalse (by intro he; injection he; contradiction)

/-- Decidable equality on lists of object members. -/
def JSON.deqMembers : (a b : List (List Nat × JSON)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | (k1, v1) :: as, (k2, v2) :: bs =>
      if hk : k1 = k2 then
        match JSON.deq v1 v2, JSON.deqMembers as bs with
        | isTrue h1, isTrue h2 => isTrue (by rw [hk, h1, h2])
        | isFalse h1, _ => isFalse (by intro he; injection he with hh _; injection hh; contradiction)
        | _, isFalse h2 => isFalse (by intro he; injection he with _ ht; contradiction)
      else isFalse (by intro he; injection he with hh _; injection hh with hk' _; contradiction)

end

instance : DecidableEq JSON := JSON.deq

/-! ## Byte and code-point constants (ASCII) -/

/-- `"` -/
abbrev quote : ℕ := 0x22
/-- `\` -/
abbrev backslash : ℕ := 0x5C
/-- `/` -/
abbrev slash : ℕ := 0x2F
/-- `{` -/
abbrev lbrace : ℕ := 0x7B
/-- `}` -/
abbrev rbrace : ℕ := 0x7D
/-- `[` -/
abbrev lbracket : ℕ := 0x5B
/-- `]` -/
abbrev rbracket : ℕ := 0x5D
/-- `:` -/
abbrev colon : ℕ := 0x3A
/-- `,` -/
abbrev comma : ℕ := 0x2C
/-- `-` -/
abbrev minus : ℕ := 0x2D
/-- `+` -/
abbrev plus : ℕ := 0x2B
/-- `.` -/
abbrev dot : ℕ := 0x2E
/-- `0` -/
abbrev digit0 : ℕ := 0x30
/-- `9` -/
abbrev digit9 : ℕ := 0x39
/-- `A` -/
abbrev upperA : ℕ := 0x41
/-- `E` -/
abbrev upperE : ℕ := 0x45
/-- `F` -/
abbrev upperF : ℕ := 0x46
/-- `a` -/
abbrev lowerA : ℕ := 0x61
/-- `b` -/
abbrev lowerB : ℕ := 0x62
/-- `e` -/
abbrev lowerE : ℕ := 0x65
/-- `f` -/
abbrev lowerF : ℕ := 0x66
/-- `n` -/
abbrev lowerN : ℕ := 0x6E
/-- `r` -/
abbrev lowerR : ℕ := 0x72
/-- `t` -/
abbrev lowerT : ℕ := 0x74
/-- `u` -/
abbrev lowerU : ℕ := 0x75
/-- space -/
abbrev space : ℕ := 0x20
/-- horizontal tab -/
abbrev tab : ℕ := 0x09
/-- line feed -/
abbrev lf : ℕ := 0x0A
/-- carriage return -/
abbrev cr : ℕ := 0x0D
/-- backspace (the value of the `\b` escape) -/
abbrev backspace : ℕ := 0x08
/-- form feed (the value of the `\f` escape) -/
abbrev formfeed : ℕ := 0x0C
/-- `~`, the last printable ASCII byte -/
abbrev tilde : ℕ := 0x7E

/-- The literal `true`. -/
abbrev trueLit : List ℕ := [lowerT, lowerR, lowerU, lowerE]
/-- The literal `false`. -/
abbrev falseLit : List ℕ := [lowerF, lowerA, 0x6C, 0x73, lowerE]
/-- The literal `null`. -/
abbrev nullLit : List ℕ := [lowerN, lowerU, 0x6C, 0x6C]

/-! ## Byte and code-point classes -/

/-- JSON insignificant whitespace: space, tab, LF, CR. -/
def isWs (c : ℕ) : Bool := c == space || c == tab || c == lf || c == cr

/-- A decimal digit. -/
def isDigit (c : ℕ) : Bool := digit0 ≤ c && c ≤ digit9

/-- A nonzero decimal digit. -/
def isDigitNz (c : ℕ) : Bool := digit0 < c && c ≤ digit9

/-- The value of a digit. -/
def digitValue (c : ℕ) : ℕ := c - digit0

/-- A hexadecimal digit (either case). -/
def isHexDigit (c : ℕ) : Bool :=
  isDigit c || (upperA ≤ c && c ≤ upperF) || (lowerA ≤ c && c ≤ lowerF)

/-- The value of a hexadecimal digit. -/
def hexValue (c : ℕ) : ℕ :=
  if isDigit c then c - digit0
  else if upperA ≤ c && c ≤ upperF then c - upperA + 10
  else c - lowerA + 10

/-- A code point that may appear unescaped inside a string: anything from
    space upwards other than `"` and `\`. -/
def isUnescaped (c : ℕ) : Bool := space ≤ c && c != quote && c != backslash

/-- A code point that may appear unescaped inside a string AND is printable
    ASCII: `isUnescaped` restricted to at most `~`. -/
def isStringByte (c : ℕ) : Bool := isUnescaped c && c ≤ tilde

/-- A UTF-16 high surrogate. -/
def isHighSurrogate (cp : ℕ) : Bool := 0xD800 ≤ cp && cp ≤ 0xDBFF
/-- A UTF-16 low surrogate. -/
def isLowSurrogate (cp : ℕ) : Bool := 0xDC00 ≤ cp && cp ≤ 0xDFFF
/-- Any UTF-16 surrogate half. -/
def isSurrogate (cp : ℕ) : Bool := isHighSurrogate cp || isLowSurrogate cp

/-! ## Stage 1: UTF-8 decoding -/

/-- An ASCII byte. -/
def isAscii (b : ℕ) : Bool := b < 0x80
/-- A UTF-8 continuation byte `10xxxxxx`. -/
def isContinuation (b : ℕ) : Bool := 0x80 ≤ b && b ≤ 0xBF
/-- A lead byte of a 2-byte sequence (`0xC0`/`0xC1` are overlong and excluded). -/
def isLead2 (b : ℕ) : Bool := 0xC2 ≤ b && b < 0xE0
/-- A lead byte of a 3-byte sequence. -/
def isLead3 (b : ℕ) : Bool := 0xE0 ≤ b && b < 0xF0
/-- A lead byte of a 4-byte sequence (`0xF5` and above are out of range). -/
def isLead4 (b : ℕ) : Bool := 0xF0 ≤ b && b < 0xF5

/-- One continuation byte, as its 6-bit payload. -/
def continuation : Parser ℕ := (· - 0x80) <$> satisfy isContinuation

/-- One UTF-8 encoded code point. Overlong encodings, surrogate halves and
    code points above `U+10FFFF` are rejected. -/
def codepoint : Parser ℕ :=
  satisfy isAscii
  <|> (do
    let b0 ← satisfy isLead2
    let b1 ← continuation
    pure ((b0 - 0xC0) * 0x40 + b1))
  <|> (do
    let b0 ← satisfy isLead3
    let b1 ← continuation
    let b2 ← continuation
    let cp := (b0 - 0xE0) * 0x1000 + b1 * 0x40 + b2
    if cp < 0x800 || isSurrogate cp then failure else pure cp)
  <|> (do
    let b0 ← satisfy isLead4
    let b1 ← continuation
    let b2 ← continuation
    let b3 ← continuation
    let cp := (b0 - 0xF0) * 0x40000 + b1 * 0x1000 + b2 * 0x40 + b3
    if cp < 0x10000 || 0x10FFFF < cp then failure else pure cp)

/-- Decode a byte list as UTF-8 into a list of Unicode code points. Returns
    `none` on any invalid, overlong, surrogate, or out-of-range sequence. -/
def utf8Decode (bytes : List ℕ) : Option (List ℕ) :=
  ((many codepoint <* eof) bytes).map (·.1)

/-! ## Stage 2: the JSON grammar, over code points -/

/-- Insignificant whitespace. -/
def ws : Parser Unit := skipWhile isWs

/-- Four hexadecimal digits, as their value. -/
def hex4 : Parser ℕ := do
  let a ← satisfy isHexDigit
  let b ← satisfy isHexDigit
  let c ← satisfy isHexDigit
  let d ← satisfy isHexDigit
  pure (((hexValue a * 16 + hexValue b) * 16 + hexValue c) * 16 + hexValue d)

/-- A `\uXXXX` escape. A high surrogate immediately followed by a `\uXXXX`
    low surrogate is combined into one code point; a lone surrogate is kept as
    is (implementation-defined by the standard). -/
def unicodeEscape : Parser ℕ := do
  byte lowerU
  let hi ← hex4
  if isHighSurrogate hi then
    let lo ← Parser.optional (do
      byte backslash; byte lowerU
      let lo ← hex4
      if isLowSurrogate lo then pure lo else failure)
    match lo with
    | some lo => pure (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))
    | none => pure hi
  else pure hi

/-- The character after a `\`. -/
def escape : Parser ℕ :=
  (byte quote *> pure quote)
  <|> (byte backslash *> pure backslash)
  <|> (byte slash *> pure slash)
  <|> (byte lowerB *> pure backspace)
  <|> (byte lowerF *> pure formfeed)
  <|> (byte lowerN *> pure lf)
  <|> (byte lowerR *> pure cr)
  <|> (byte lowerT *> pure tab)
  <|> unicodeEscape

/-- One element of a string body: an unescaped code point or an escape. -/
def stringElem : Parser ℕ := satisfy isUnescaped <|> (byte backslash *> escape)

/-- A JSON string, returning its decoded code points. -/
def string : Parser (List ℕ) := byte quote *> many stringElem <* byte quote

/-- One or more digits, as their values. -/
def digits1 : Parser (List ℕ) := do
  let d ← satisfy isDigit
  let ds ← many (satisfy isDigit)
  pure ((d :: ds).map digitValue)

/-- The integer part of a number: `0` (not followed by a digit) or
    `[1-9][0-9]*`, as digit values. -/
def intDigits : Parser (List ℕ) :=
  (byte digit0 *> notFollowedBy isDigit *> pure [0])
  <|> (do
    let d ← satisfy isDigitNz
    let ds ← many (satisfy isDigit)
    pure ((d :: ds).map digitValue))

/-- The exponent part: `e`/`E`, an optional sign, one or more digits. Returns
    whether the exponent is negative (a `+` or absent sign gives `false`) and
    its digits. -/
def exponent : Parser (Bool × List ℕ) := do
  byte lowerE <|> byte upperE
  let neg ← (byte plus *> pure false) <|> (byte minus *> pure true) <|> pure false
  let ds ← digits1
  pure (neg, ds)

/-- A JSON number. Rejects leading zeros, a leading `+`, a bare `.`, trailing
    dots, and empty exponents. -/
def number : Parser JNumber := do
  let neg ← Parser.optional (byte minus)
  let ints ← intDigits
  let frac ← Parser.optional (byte dot *> digits1)
  let exp ← Parser.optional exponent
  pure { negative := neg.isSome, intDigits := ints, fracDigits := frac.getD [],
         expNegative := (exp.map (·.1)).getD false, expDigits := (exp.map (·.2)).getD [] }

mutual

/-- A JSON value, after leading whitespace. `fuel` bounds the nesting depth. -/
def value : ℕ → Parser JSON
  | 0 => fail
  | fuel + 1 =>
    ws *> (
      (JSON.obj <$> object fuel)
      <|> (JSON.arr <$> array fuel)
      <|> (JSON.str <$> string)
      <|> (literal trueLit *> pure (JSON.bool true))
      <|> (literal falseLit *> pure (JSON.bool false))
      <|> (literal nullLit *> pure JSON.null)
      <|> (JSON.num <$> number))

/-- An array: `[` values separated by `,` `]`. -/
def array (fuel : ℕ) : Parser (List JSON) :=
  byte lbracket *> sepBy (value fuel) (ws *> byte comma) <* ws <* byte rbracket

/-- One object member: `"key" : value`. -/
def member (fuel : ℕ) : Parser (List ℕ × JSON) := do
  ws
  let key ← string
  ws; byte colon
  let v ← value fuel
  pure (key, v)

/-- An object: `{` members separated by `,` `}`. -/
def object (fuel : ℕ) : Parser (List (List ℕ × JSON)) :=
  byte lbrace *> sepBy (member fuel) (ws *> byte comma) <* ws <* byte rbrace

end

/-- A whole document: one value surrounded by whitespace, consuming the entire
    input. -/
def document (cps : List ℕ) : Option (JSON × List ℕ) :=
  (value (cps.length + 1) <* ws <* eof) cps

/-! ## Top level -/

/-- Parse a byte list as a complete JSON document. Returns `none` unless the
    entire input (modulo leading/trailing whitespace) is a single JSON value. -/
def parseBytes (bytes : List ℕ) : Option JSON :=
  (utf8Decode bytes).bind fun cps => (document cps).map (·.1)

/-- Parse a byte vector as a complete JSON document. -/
def parse {n : ℕ} (input : Vector ℕ n) : Option JSON := parseBytes input.toList

/-- `parse?` is a synonym for `parse`. -/
@[reducible] def parse? {n : ℕ} (input : Vector ℕ n) : Option JSON := parse input

end Specs.JSON
