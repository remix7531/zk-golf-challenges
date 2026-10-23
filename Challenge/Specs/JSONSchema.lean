import Challenge.Specs.JSON

/-!
# Schema-directed views of a parsed JSON object

A `Schema` is a table of known keys, each with a `ValueSpec` saying what
shape its value must have. `IsToken S j` says that the parsed document `j` is
a flat object every known key of which carries an admissible value; unknown
keys are allowed (their values only have to be scalars, so the document stays
flat) and keys may appear in any order. `lookup` reads a key back.

The predicate deliberately assumes as little as possible: no key is required,
known keys are only required to be unique (so `lookup` is unambiguous), and
nothing is said about the relation between values. Anything a consumer wants
to check about the extracted values is the consumer's business.
-/

namespace Specs.JSONSchema

open Specs.JSON (JSON JNumber)

/-- Bytes of an ASCII key. -/
def key (s : String) : List ℕ := s.toList.map Char.toNat

/-- The admissible shapes of a known key's value. -/
inductive ValueSpec where
  /-- an ASCII string of at most `maxLen` code points -/
  | str (maxLen : ℕ)
  /-- an integer (no fraction, no exponent) of at most `maxDigits` digits -/
  | int (maxDigits : ℕ)
  /-- `true` or `false` -/
  | bool
deriving DecidableEq, Repr

/-- A known key and the shape of its value. -/
structure Field where
  name : List ℕ
  spec : ValueSpec
deriving DecidableEq, Repr

/-- A table of known keys and a cap on the total number of members. -/
structure Schema where
  fields : List Field
  maxMembers : ℕ
deriving Repr

/-- Every code point is ASCII. -/
def IsAscii (s : List ℕ) : Prop := ∀ c ∈ s, c < 0x80

instance : DecidablePred IsAscii := fun s => by unfold IsAscii; infer_instance

/-- A parsed value has the shape a `ValueSpec` asks for. -/
def ValueSpec.Holds : ValueSpec → JSON → Prop
  | .str n, .str s => IsAscii s ∧ s.length ≤ n
  | .int d, .num m => m.fracDigits = [] ∧ m.expDigits = [] ∧ m.intDigits.length ≤ d
  | .bool, .bool _ => True
  | _, _ => False

instance (v : ValueSpec) : DecidablePred v.Holds := fun j => by
  cases v <;> cases j <;> simp only [ValueSpec.Holds] <;> infer_instance

/-- A scalar value: anything but an array or an object. -/
def IsScalar : JSON → Prop
  | .arr _ => False
  | .obj _ => False
  | _ => True

instance : DecidablePred IsScalar := fun j => by
  cases j <;> simp only [IsScalar] <;> infer_instance

/-- The known field with this name, if any. -/
def Schema.field? (S : Schema) (name : List ℕ) : Option Field :=
  S.fields.find? fun f => f.name = name

/-- What a member's value must satisfy: the spec of its key if the key is
    known, otherwise only that it is a scalar. -/
def Schema.MemberOk (S : Schema) (m : List ℕ × JSON) : Prop :=
  match S.field? m.1 with
  | some f => f.spec.Holds m.2
  | none => IsScalar m.2

instance (S : Schema) : DecidablePred S.MemberOk := fun m => by
  unfold Schema.MemberOk
  cases S.field? m.1 <;> infer_instance

/-- A parsed document is a token of the schema: a flat object of at most
    `maxMembers` members, every known key occurring at most once, every
    member's value admissible for its key. -/
def IsToken (S : Schema) : JSON → Prop
  | .obj ms =>
    ms.length ≤ S.maxMembers ∧
    (∀ f ∈ S.fields, (ms.filter fun m => m.1 = f.name).length ≤ 1) ∧
    ∀ m ∈ ms, S.MemberOk m
  | _ => False

instance (S : Schema) : DecidablePred (IsToken S) := fun j => by
  cases j <;> simp only [IsToken] <;> infer_instance

/-! ## Reading values back -/

/-- The value of a key, if present (the first occurrence; unique for known
    keys of a token). -/
def lookup (ms : List (List ℕ × JSON)) (name : List ℕ) : Option JSON :=
  (ms.find? fun m => m.1 = name).map (·.2)

/-- The code points of a string value. -/
def asString : JSON → Option (List ℕ)
  | .str s => some s
  | _ => none

/-- The sign and decimal digits (values `0`–`9`) of an integer value. -/
def asInt : JSON → Option (Bool × List ℕ)
  | .num n => some (n.negative, n.intDigits)
  | _ => none

/-- A boolean value. -/
def asBool : JSON → Option Bool
  | .bool b => some b
  | _ => none

/-- The members of an object (none for any other value). -/
def members : JSON → List (List ℕ × JSON)
  | .obj ms => ms
  | _ => []

end Specs.JSONSchema
