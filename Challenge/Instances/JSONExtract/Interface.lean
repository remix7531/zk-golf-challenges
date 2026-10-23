import Challenge.Specs.JSONExtract
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS


/-!
Public interface for the Google ID token claims extraction instance.

This file is the trusted boundary: it owns the input/output type and the
statements the implementation must prove. The implementation may be arbitrary,
but its exported proofs must have exactly these types.
-/

namespace Challenge.Instances.JSONExtract

namespace Interface

open Specs.JSONExtract (issMax subMax audMax hdMax emailMax nonceMax atHashMax timeMax)

/-- Fixed byte-buffer length for this instance. -/
@[reducible] def bufferLen : ℕ := 1024

/--
Inputs to the extractor.

`buffer` is the raw byte string (the decoded JWT payload) encoded as field
elements; `len` is the length of the buffer prefix to parse.
-/
structure Input (F : Type) where
  buffer : Vector F bufferLen
  len : F
deriving ProvableStruct

/-- A string claim: presence flag, length, zero-padded bytes. -/
structure StrSlot (n : ℕ) (F : Type) where
  present : F
  len : F
  bytes : Vector F n
deriving ProvableStruct

/-- An integer claim: presence flag, sign flag, digit count, zero-padded
    decimal digit values. -/
structure IntSlot (n : ℕ) (F : Type) where
  present : F
  negative : F
  len : F
  digits : Vector F n
deriving ProvableStruct

/-- A boolean claim: presence flag and value. -/
structure BoolSlot (F : Type) where
  present : F
  value : F
deriving ProvableStruct

/-- Output of the extractor: one slot per claim of `Specs.JSONExtract.google`. -/
structure Output (F : Type) where
  iss : StrSlot issMax F
  sub : StrSlot subMax F
  aud : StrSlot audMax F
  azp : StrSlot audMax F
  hd : StrSlot hdMax F
  email : StrSlot emailMax F
  emailVerified : BoolSlot F
  nonce : StrSlot nonceMax F
  atHash : StrSlot atHashMax F
  iat : IntSlot timeMax F
  exp : IntSlot timeMax F
deriving ProvableStruct

section

-- we are working over the circom prime
def circomPrime : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

axiom hCircomPrime : circomPrime.Prime
instance : Fact circomPrime.Prime := ⟨hCircomPrime⟩

/--
  Interpret a field-element vector as the corresponding natural values.
-/
def fieldElemsToNat {n : ℕ} (xs : Vector (F circomPrime) n) : Vector ℕ n :=
  xs.map ZMod.val

/-- Read a field-element string slot as nats. -/
def strSlotToNats {n : ℕ} (x : StrSlot n (F circomPrime)) : Specs.JSONExtract.StrSlot n :=
  ⟨x.present.val, x.len.val, x.bytes.map ZMod.val⟩

/-- Read a field-element integer slot as nats. -/
def intSlotToNats {n : ℕ} (x : IntSlot n (F circomPrime)) : Specs.JSONExtract.IntSlot n :=
  ⟨x.present.val, x.negative.val, x.len.val, x.digits.map ZMod.val⟩

/-- Read a field-element boolean slot as nats. -/
def boolSlotToNats (x : BoolSlot (F circomPrime)) : Specs.JSONExtract.BoolSlot :=
  ⟨x.present.val, x.value.val⟩

/-- Read the field-element `Output` as an `ExpectedOutput` of nats. -/
def outputToNats (output : Output (F circomPrime)) : Specs.JSONExtract.ExpectedOutput where
  iss := strSlotToNats output.iss
  sub := strSlotToNats output.sub
  aud := strSlotToNats output.aud
  azp := strSlotToNats output.azp
  hd := strSlotToNats output.hd
  email := strSlotToNats output.email
  emailVerified := boolSlotToNats output.emailVerified
  nonce := strSlotToNats output.nonce
  atHash := strSlotToNats output.atHash
  iat := intSlotToNats output.iat
  exp := intSlotToNats output.exp

def Assumptions (input : Input (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop :=
  -- the buffer is a byte string and the length is in bounds (at most
  -- `bufferLen`, so the prefix may span the whole buffer); we do NOT assume the
  -- input is valid JSON.
  Specs.JSONExtract.IsByteArray (fieldElemsToNat input.buffer) ∧ input.len.val ≤ bufferLen

def Spec (input : Input (F circomPrime)) (output : Output (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop :=
  -- `len ≤ bufferLen`, matching `Assumptions`: the parsed prefix may cover the
  -- whole buffer, so a document of exactly `bufferLen` bytes is in scope.
  if h : input.len.val ≤ bufferLen then
    let pre := Specs.JSONExtract.takePrefix (fieldElemsToNat input.buffer) input.len.val h
    -- parse the prefix as JSON; the parse must be a token of the Google schema
    -- and the output is the encoding of the claims read out of it
    match Specs.JSON.parseBytes pre.toList with
    | some j =>
      Specs.JSONSchema.IsToken Specs.JSONExtract.google j ∧
      outputToNats output = Specs.JSONExtract.encodeOutput (Specs.JSONExtract.GoogleClaims.ofJSON j)
    | none => False
  else
    False

def ProverAssumptions
    (input : Input (F circomPrime)) (data : ProverData (F circomPrime)) (_hint : ProverHint (F circomPrime)) : Prop :=
  -- the honest inputs satisfy the assumptions
  Assumptions input data ∧
  -- the honest prover supplies a token of the Google schema
  (if h : input.len.val ≤ bufferLen then
      let pre := Specs.JSONExtract.takePrefix (fieldElemsToNat input.buffer) input.len.val h
      match Specs.JSON.parseBytes pre.toList with
      | some j => Specs.JSONSchema.IsToken Specs.JSONExtract.google j
      | none => False
   else False) ∧
  -- the honest prover pads the data with zeros past the length
  ∀ (i : Fin bufferLen), i >= input.len.val → input.buffer[i]'(i.isLt) = 0

def ProverSpec
    (_input : Input (F circomPrime)) (_output : Output (F circomPrime)) (_hint : ProverHint (F circomPrime)) : Prop :=
  True

end

end Interface
end Challenge.Instances.JSONExtract
