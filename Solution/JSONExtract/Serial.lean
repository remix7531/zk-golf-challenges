import Solution.JSONExtract.Model

/-!
# The serialization view of an accepting run (`JSONExtract`)

The byte automaton of `Model.lean` recognises exactly the byte strings of a
*flat* JSON object whose members obey the type gates of the Google schema.
This file gives that language a name: a `Ser` is the structure of one such byte
string (whitespace runs, key/value string bodies broken into their pieces,
numbers broken into their digit lists), `Ser.bytes` flattens it back to bytes,
`Ser.WF` says the pieces are in range, and `Ser.json` is the JSON value the
trusted parser reads out of it.

Nothing here mentions the automaton or the parser; the two directions
(`run ↔ Ser` and `Ser ↔ parse`) live in the files that follow.
-/

namespace Solution.JSONExtract

namespace Serial

open Specs.JSON
open Model (Claim nClaims claimName claimCap isStrClaim isIntClaim isBoolClaim)

/-! ## String-body elements

One element of a JSON string body, as the *byte* automaton sees it: a raw
printable byte, a simple escape, a `\uXXXX` escape, or a 2/3/4-byte UTF-8
sequence. -/

inductive SE where
  /-- a byte standing for itself (`isUnescaped`) -/
  | plain (b : ℕ)
  /-- `\b` for one of the eight simple escapes -/
  | esc (b : ℕ)
  /-- `ꯍ` -/
  | hex (a b c d : ℕ)
  | u2 (b0 b1 : ℕ)
  | u3 (b0 b1 b2 : ℕ)
  | u4 (b0 b1 b2 b3 : ℕ)
deriving Repr, DecidableEq

/-- The bytes of a string-body element. -/
def SE.bytes : SE → List ℕ
  | .plain b => [b]
  | .esc b => [backslash, b]
  | .hex a b c d => [backslash, lowerU, a, b, c, d]
  | .u2 b0 b1 => [b0, b1]
  | .u3 b0 b1 b2 => [b0, b1, b2]
  | .u4 b0 b1 b2 b3 => [b0, b1, b2, b3]

/-- The value of four hex digits. -/
def hexNum (a b c d : ℕ) : ℕ :=
  ((Model.hexVal a * 16 + Model.hexVal b) * 16 + Model.hexVal c) * 16 + Model.hexVal d

/-- Every byte of the element is in the class the automaton demands. -/
def SE.WF : SE → Prop
  | .plain b => Model.isUnescaped b = true
  | .esc b => Model.isSimpleEsc b = true
  | .hex a b c d =>
      Model.isHex a = true ∧ Model.isHex b = true ∧ Model.isHex c = true ∧ Model.isHex d = true
  | .u2 b0 b1 => Model.isLead2 b0 = true ∧ Model.isCont b1 = true
  | .u3 b0 b1 b2 =>
      ((b0 = 0xE0 ∧ Model.isContA0BF b1 = true) ∨
        (Model.isLead3 b0 = true ∧ Model.isCont b1 = true) ∨
        (b0 = 0xED ∧ Model.isCont809F b1 = true)) ∧ Model.isCont b2 = true
  | .u4 b0 b1 b2 b3 =>
      ((b0 = 0xF0 ∧ Model.isCont90BF b1 = true) ∨
        (Model.isLead4 b0 = true ∧ Model.isCont b1 = true) ∨
        (b0 = 0xF4 ∧ Model.isCont808F b1 = true)) ∧
        Model.isCont b2 = true ∧ Model.isCont b3 = true

instance : DecidablePred SE.WF := fun e => by cases e <;> unfold SE.WF <;> infer_instance

/-- The code point the *model* emits for an element: a UTF-8 sequence is only
recorded as "not ASCII". -/
def SE.mcp : SE → ℕ
  | .plain b => b
  | .esc b => Model.escVal b
  | .hex a b c d => hexNum a b c d
  | .u2 _ _ => Model.nonAsciiMarker
  | .u3 _ _ _ => Model.nonAsciiMarker
  | .u4 _ _ _ _ => Model.nonAsciiMarker

/-- The code point the *specification* decodes for an element (before surrogate
pairing). -/
def SE.scp : SE → ℕ
  | .plain b => b
  | .esc b => Model.escVal b
  | .hex a b c d => hexNum a b c d
  | .u2 b0 b1 => (b0 - 0xC0) * 0x40 + (b1 - 0x80)
  | .u3 b0 b1 b2 => (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)
  | .u4 b0 b1 b2 b3 =>
      (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80)

/-- The code points the UTF-8 decoder produces for an element: an escape is
still a backslash followed by its characters. -/
def SE.dcps : SE → List ℕ
  | .plain b => [b]
  | .esc b => [backslash, b]
  | .hex a b c d => [backslash, lowerU, a, b, c, d]
  | .u2 b0 b1 => [SE.scp (.u2 b0 b1)]
  | .u3 b0 b1 b2 => [SE.scp (.u3 b0 b1 b2)]
  | .u4 b0 b1 b2 b3 => [SE.scp (.u4 b0 b1 b2 b3)]

/-- The code points of a string body, before parsing. -/
def dcpsList (l : List SE) : List ℕ := (l.map SE.dcps).flatten

/-- Is this element a `\uXXXX` escape whose value is a UTF-16 high surrogate? -/
def SE.isHigh : SE → Bool
  | .hex a b c d => isHighSurrogate (hexNum a b c d)
  | _ => false

/-- Is this element a `\uXXXX` escape whose value is a UTF-16 low surrogate? -/
def SE.isLow : SE → Bool
  | .hex a b c d => isLowSurrogate (hexNum a b c d)
  | _ => false

/-- The code points the specification decodes from a string body: a `\uXXXX`
high surrogate immediately followed by a `\uXXXX` low surrogate is combined
into one code point. -/
def specCps : List SE → List ℕ
  | [] => []
  | [e] => [e.scp]
  | e :: e' :: rest =>
      if e.isHigh && e'.isLow then
        (0x10000 + (e.scp - 0xD800) * 0x400 + (e'.scp - 0xDC00)) :: specCps rest
      else e.scp :: specCps (e' :: rest)

/-- The code points the *model* emits for a string body. -/
def mcps (l : List SE) : List ℕ := l.map SE.mcp

/-- The bytes of a string body. -/
def seBytes (l : List SE) : List ℕ := (l.map SE.bytes).flatten

/-! ## Numbers -/

/-- The exponent part of a number: the letter byte, the optional sign byte and
the digit values. -/
structure SExp where
  letter : ℕ
  sign : Option ℕ
  digits : List ℕ
deriving Repr, DecidableEq

/-- A number, broken into the pieces the automaton reads. Digits are stored as
*values* (`0`–`9`), as the specification does. -/
structure SNum where
  neg : Bool
  ints : List ℕ
  /-- the fractional digits; `[]` means there is no `.` at all -/
  frac : List ℕ
  /-- the exponent, `none` when absent -/
  exp : Option SExp
deriving Repr, DecidableEq

/-- Digit values as code points. -/
def digitsOf (ds : List ℕ) : List ℕ := ds.map (· + digit0)

def SExp.bytes (e : SExp) : List ℕ :=
  e.letter :: ((match e.sign with | none => [] | some s => [s]) ++ e.digits.map (· + digit0))

def SNum.bytes (n : SNum) : List ℕ :=
  (if n.neg then [minus] else []) ++ n.ints.map (· + digit0) ++
    (if n.frac = [] then [] else dot :: n.frac.map (· + digit0)) ++
    (match n.exp with | none => [] | some e => e.bytes)

/-- The integer part is `0` or a nonzero-leading digit string. -/
def SNum.WF (n : SNum) : Prop :=
  (n.ints = [0] ∨ (∃ d ds, n.ints = d :: ds ∧ 1 ≤ d ∧ d ≤ 9 ∧ ∀ x ∈ ds, x ≤ 9)) ∧
  (∀ x ∈ n.frac, x ≤ 9) ∧
  (match n.exp with
    | none => True
    | some e => (e.letter = lowerE ∨ e.letter = upperE) ∧
        (match e.sign with | none => True | some s => s = plus ∨ s = minus) ∧
        e.digits ≠ [] ∧ ∀ x ∈ e.digits, x ≤ 9)

/-! ## Values -/

inductive SV where
  | str (body : List SE)
  | num (n : SNum)
  | btrue
  | bfalse
  | null
deriving Repr, DecidableEq

def SV.bytes : SV → List ℕ
  | .str body => quote :: (seBytes body ++ [quote])
  | .num n => n.bytes
  | .btrue => trueLit
  | .bfalse => falseLit
  | .null => nullLit

/-- The pieces of the value are in range. -/
def SV.WF : SV → Prop
  | .str body => ∀ e ∈ body, e.WF
  | .num n => n.WF
  | _ => True

/-- The code points (or digits) the model routes for this value. -/
def SV.vals : SV → List ℕ
  | .str body => mcps body
  | .num n => n.ints
  | _ => []

/-- The sign flag the model reads for this value. -/
def SV.sign : SV → ℕ
  | .num n => if n.neg then 1 else 0
  | _ => 0

/-- The boolean flag the model reads for this value. -/
def SV.trues : SV → ℕ
  | .btrue => 1
  | _ => 0

/-- The JSON value a serialized value denotes. -/
def SV.json : SV → JSON
  | .str body => .str (specCps body)
  | .num n => .num
      { negative := n.neg, intDigits := n.ints, fracDigits := n.frac,
        expNegative := (n.exp.map fun e => decide (e.sign = some minus)).getD false,
        expDigits := (n.exp.map (·.digits)).getD [] }
  | .btrue => .bool true
  | .bfalse => .bool false
  | .null => .null

/-! ## Members and the whole document -/

structure SMem where
  /-- whitespace before the key's opening quote -/
  ws0 : List ℕ
  key : List SE
  /-- whitespace between the key and the `:` -/
  ws1 : List ℕ
  /-- whitespace between the `:` and the value -/
  ws2 : List ℕ
  val : SV
  /-- whitespace after the value -/
  ws3 : List ℕ

def SMem.bytes (m : SMem) : List ℕ :=
  m.ws0 ++ [quote] ++ seBytes m.key ++ [quote] ++ m.ws1 ++ [colon] ++ m.ws2 ++
    m.val.bytes ++ m.ws3

/-- The key as the model reads it. -/
def SMem.mkey (m : SMem) : List ℕ := mcps m.key
/-- The key as the specification reads it. -/
def SMem.skey (m : SMem) : List ℕ := specCps m.key

/-- The known claim this member's key names, if any. -/
def SMem.claim (m : SMem) : Option Claim :=
  (List.finRange nClaims).find? fun k => decide (m.mkey = claimName k)

/-- The value is admissible for the claim the key names. -/
def SV.Ok (c : Option Claim) (v : SV) : Prop :=
  match c with
  | none => True
  | some k =>
      if isStrClaim k then
        ∃ body, v = .str body ∧ (∀ e ∈ body, e.mcp < 0x80) ∧ body.length ≤ claimCap k
      else if isIntClaim k then
        ∃ n, v = .num n ∧ n.frac = [] ∧ n.exp = none ∧ n.ints.length ≤ claimCap k
      else v = .btrue ∨ v = .bfalse

/-- The value is admissible for the member's key. -/
def SMem.ValOk (m : SMem) : Prop := m.val.WF ∧ SV.Ok m.claim m.val

/-- Every byte of the list is JSON whitespace. -/
def IsWs (l : List ℕ) : Prop := ∀ b ∈ l, Model.isWs b = true

def SMem.WF (m : SMem) : Prop :=
  IsWs m.ws0 ∧ IsWs m.ws1 ∧ IsWs m.ws2 ∧ IsWs m.ws3 ∧ (∀ e ∈ m.key, e.WF) ∧ m.ValOk

/-- A whole accepted byte string: leading whitespace, `{`, the members
separated by `,` (or a whitespace run when there is no member), `}`, trailing
whitespace. -/
structure Ser where
  pre : List ℕ
  body : List SMem
  /-- the whitespace inside `{ }` when there is no member -/
  wsEmpty : List ℕ
  post : List ℕ

def bodyBytes (ms : List SMem) (we : List ℕ) : List ℕ :=
  match ms with
  | [] => we
  | m :: ms => m.bytes ++ (ms.map fun m' => comma :: m'.bytes).flatten

def Ser.bytes (s : Ser) : List ℕ :=
  s.pre ++ [lbrace] ++ bodyBytes s.body s.wsEmpty ++ [rbrace] ++ s.post

def Ser.WF (s : Ser) : Prop :=
  IsWs s.pre ∧ IsWs s.wsEmpty ∧ IsWs s.post ∧ (∀ m ∈ s.body, m.WF) ∧
    s.body.length ≤ Specs.JSONExtract.maxMembers ∧
    ∀ k : Claim, (s.body.filter fun m => decide (m.claim = some k)).length ≤ 1

/-- Well-formedness without the two caps (member count and key uniqueness). -/
def Ser.SWF (s : Ser) : Prop :=
  IsWs s.pre ∧ IsWs s.wsEmpty ∧ IsWs s.post ∧ ∀ m ∈ s.body, m.WF

theorem Ser.swf_of_wf {s : Ser} (h : s.WF) : s.SWF := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-! ## The slots of a serialization -/

/-- How many members carry claim `k` (`0` or `1` for a well-formed `Ser`). -/
def bMatch (ms : List SMem) (k : Claim) : ℕ :=
  (ms.map fun m => if m.claim = some k then 1 else 0).sum
/-- The values routed to claim `k`. -/
def bVals (ms : List SMem) (k : Claim) : List ℕ :=
  (ms.map fun m => if m.claim = some k then m.val.vals else []).flatten
/-- The sign flag of claim `k`. -/
def bSign (ms : List SMem) (k : Claim) : ℕ :=
  (ms.map fun m => if m.claim = some k then m.val.sign else 0).sum
/-- The boolean flag of claim `k`. -/
def bTrue (ms : List SMem) (k : Claim) : ℕ :=
  (ms.map fun m => if m.claim = some k then m.val.trues else 0).sum

/-- Claim `k`'s string slot, read off the serialization. -/
def strSlotOf (ms : List SMem) (k : Claim) (n : ℕ) : Specs.JSONExtract.StrSlot n where
  present := bMatch ms k
  len := (bVals ms k).length
  bytes := Vector.ofFn fun t : Fin n => (bVals ms k).getD t.val 0

/-- Claim `k`'s integer slot, read off the serialization. -/
def intSlotOf (ms : List SMem) (k : Claim) (n : ℕ) : Specs.JSONExtract.IntSlot n where
  present := bMatch ms k
  negative := bSign ms k
  len := (bVals ms k).length
  digits := Vector.ofFn fun t : Fin n => (bVals ms k).getD t.val 0

/-- Claim `k`'s boolean slot, read off the serialization. -/
def boolSlotOf (ms : List SMem) (k : Claim) : Specs.JSONExtract.BoolSlot where
  present := bMatch ms k
  value := bTrue ms k

/-- The whole output, read off the serialization. -/
def outputOf (ms : List SMem) : Specs.JSONExtract.ExpectedOutput where
  iss := strSlotOf ms 0 _
  sub := strSlotOf ms 1 _
  aud := strSlotOf ms 2 _
  azp := strSlotOf ms 3 _
  hd := strSlotOf ms 4 _
  email := strSlotOf ms 5 _
  emailVerified := boolSlotOf ms 6
  nonce := strSlotOf ms 7 _
  atHash := strSlotOf ms 8 _
  iat := intSlotOf ms 9 _
  exp := intSlotOf ms 10 _

/-- The JSON document a serialization denotes. -/
def Ser.json (s : Ser) : JSON := .obj (s.body.map fun m => (m.skey, m.val.json))

end Serial

end Solution.JSONExtract
