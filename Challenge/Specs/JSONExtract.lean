import Challenge.Specs.JSONSchema

/-!
# Google ID token claims extraction

The challenge reads the JSON payload of a Google ID token (the claims object
of the JWT, already base64url-decoded) and extracts the claims of interest.
On top of the generic parser `Specs.JSON.parseBytes` and the schema layer
`Specs.JSONSchema`, this file fixes:

* the schema `google`: the known claims, the shape and size cap of each, and
  the cap on the number of members. Keys may appear in any order, none is
  required, and unknown claims are allowed as long as they are scalars;
* the extracted data, `GoogleClaims`: one optional slot per known claim,
  read back from the parsed object with `GoogleClaims.ofJSON`;
* the fixed-shape encoding of a `GoogleClaims` for the circuit output
  (`encodeOutput`): each string claim as a presence flag, a length and a
  padded byte slot, each integer claim as a presence flag, a sign, a digit
  count and a padded slot of decimal digit values, each boolean claim as a
  presence flag and a bit.

The challenge `Spec` parses the input, requires `IsToken google` of the
parse, and compares the output with `encodeOutput (GoogleClaims.ofJSON j)`.
The predicate assumes nothing beyond what makes the extraction well defined
(types, size caps, uniqueness of known keys, flatness); in particular the
issuer is extracted, not checked, and no relation between claims is assumed.
-/

namespace Specs.JSONExtract

open Specs.JSON (JSON)
open Specs.JSONSchema

/-! ## The schema -/

/-- Size cap (code points) of the `iss` claim (`https://accounts.google.com`). -/
@[reducible] def issMax : ℕ := 32
/-- Size cap of the `sub` claim (a decimal subject id, 21 digits in practice). -/
@[reducible] def subMax : ℕ := 32
/-- Size cap of the `aud` and `azp` claims (an OAuth client id). -/
@[reducible] def audMax : ℕ := 128
/-- Size cap of the `hd` claim (a hosted domain). -/
@[reducible] def hdMax : ℕ := 64
/-- Size cap of the `email` claim. -/
@[reducible] def emailMax : ℕ := 128
/-- Size cap of the `nonce` claim. -/
@[reducible] def nonceMax : ℕ := 64
/-- Size cap of the `at_hash` claim. -/
@[reducible] def atHashMax : ℕ := 64
/-- Digit cap of the `iat` and `exp` claims (Unix timestamps). -/
@[reducible] def timeMax : ℕ := 12
/-- Cap on the number of members of the claims object. Google's OpenID Connect
    reference documents 19 ID-token claims (5 always present, 14 optional, among
    them `amr` and `auth_time`) and real Workspace tokens carry 16 today, so 32
    leaves margin for Google adding claims. -/
@[reducible] def maxMembers : ℕ := 32

/-- The Google ID token schema. -/
def google : Schema where
  fields := [
    ⟨key "iss", .str issMax⟩,
    ⟨key "sub", .str subMax⟩,
    ⟨key "aud", .str audMax⟩,
    ⟨key "azp", .str audMax⟩,
    ⟨key "hd", .str hdMax⟩,
    ⟨key "email", .str emailMax⟩,
    ⟨key "email_verified", .bool⟩,
    ⟨key "nonce", .str nonceMax⟩,
    ⟨key "at_hash", .str atHashMax⟩,
    ⟨key "iat", .int timeMax⟩,
    ⟨key "exp", .int timeMax⟩]
  maxMembers := maxMembers

/-! ## The extracted claims -/

/-- The claims of interest, each present or not. Strings are ASCII code
    points; integers are a sign flag and decimal digit values. -/
structure GoogleClaims where
  iss : Option (List ℕ)
  sub : Option (List ℕ)
  aud : Option (List ℕ)
  azp : Option (List ℕ)
  hd : Option (List ℕ)
  email : Option (List ℕ)
  emailVerified : Option Bool
  nonce : Option (List ℕ)
  atHash : Option (List ℕ)
  iat : Option (Bool × List ℕ)
  exp : Option (Bool × List ℕ)
deriving DecidableEq, Repr

/-- Read the claims out of a parsed document. -/
def GoogleClaims.ofJSON (j : JSON) : GoogleClaims :=
  let ms := members j
  { iss := (lookup ms (key "iss")).bind asString
    sub := (lookup ms (key "sub")).bind asString
    aud := (lookup ms (key "aud")).bind asString
    azp := (lookup ms (key "azp")).bind asString
    hd := (lookup ms (key "hd")).bind asString
    email := (lookup ms (key "email")).bind asString
    emailVerified := (lookup ms (key "email_verified")).bind asBool
    nonce := (lookup ms (key "nonce")).bind asString
    atHash := (lookup ms (key "at_hash")).bind asString
    iat := (lookup ms (key "iat")).bind asInt
    exp := (lookup ms (key "exp")).bind asInt }

/-! ## Output encoding (at the nat level) -/

/-- An octet string represented as a vector of natural numbers. -/
@[reducible] def IsByteArray {n : ℕ} (xs : Vector ℕ n) : Prop :=
  ∀ i : Fin n, xs[i] < 256

/-- Truncate or zero-pad a byte list to a fixed length `n`. -/
def padTo (l : List ℕ) (n : ℕ) : Vector ℕ n :=
  Vector.ofFn fun i => l.getD i.val 0

/-- Take the first `len` bytes of a fixed-size buffer. -/
def takePrefix {bufferLen : ℕ} (input : Vector ℕ bufferLen) (len : ℕ)
    (h : len ≤ bufferLen) : Vector ℕ len :=
  Vector.ofFn fun i => input[i.val]'(Nat.lt_of_lt_of_le i.isLt h)

/-- A string claim: presence flag, length, zero-padded bytes. -/
structure StrSlot (n : ℕ) where
  present : ℕ
  len : ℕ
  bytes : Vector ℕ n
deriving DecidableEq, Repr

/-- An integer claim: presence flag, sign flag, digit count, zero-padded
    decimal digit values. -/
structure IntSlot (n : ℕ) where
  present : ℕ
  negative : ℕ
  len : ℕ
  digits : Vector ℕ n
deriving DecidableEq, Repr

/-- A boolean claim: presence flag and value. -/
structure BoolSlot where
  present : ℕ
  value : ℕ
deriving DecidableEq, Repr

/-- Encode an optional string claim. -/
def encodeStr {n : ℕ} : Option (List ℕ) → StrSlot n
  | none => ⟨0, 0, padTo [] n⟩
  | some s => ⟨1, s.length, padTo s n⟩

/-- Encode an optional integer claim. -/
def encodeInt {n : ℕ} : Option (Bool × List ℕ) → IntSlot n
  | none => ⟨0, 0, 0, padTo [] n⟩
  | some (neg, ds) => ⟨1, if neg then 1 else 0, ds.length, padTo ds n⟩

/-- Encode an optional boolean claim. -/
def encodeBool : Option Bool → BoolSlot
  | none => ⟨0, 0⟩
  | some b => ⟨1, if b then 1 else 0⟩

/-- The canonical output: one slot per claim. -/
structure ExpectedOutput where
  iss : StrSlot issMax
  sub : StrSlot subMax
  aud : StrSlot audMax
  azp : StrSlot audMax
  hd : StrSlot hdMax
  email : StrSlot emailMax
  emailVerified : BoolSlot
  nonce : StrSlot nonceMax
  atHash : StrSlot atHashMax
  iat : IntSlot timeMax
  exp : IntSlot timeMax
deriving DecidableEq, Repr

/-- Encode the extracted claims into the canonical output. -/
def encodeOutput (c : GoogleClaims) : ExpectedOutput where
  iss := encodeStr c.iss
  sub := encodeStr c.sub
  aud := encodeStr c.aud
  azp := encodeStr c.azp
  hd := encodeStr c.hd
  email := encodeStr c.email
  emailVerified := encodeBool c.emailVerified
  nonce := encodeStr c.nonce
  atHash := encodeStr c.atHash
  iat := encodeInt c.iat
  exp := encodeInt c.exp

end Specs.JSONExtract
