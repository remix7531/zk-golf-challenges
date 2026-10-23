import Challenge.Specs.JSONExtract

/-!
Test vectors for the Google ID token claims extraction. Inputs are written as
strings and turned into byte lists with `bytes`; `native_decide` evaluates the
parser. `accept` packages parsing, the token predicate and the claim read-out
the way the challenge `Spec` does.
-/

namespace Specs.JSONExtract.Tests

open Specs.JSONExtract Specs.JSONSchema

/-- The UTF-8 bytes of a string. -/
def bytes (s : String) : List ℕ := s.toUTF8.toList.map UInt8.toNat

/-- Parse, require `IsToken google`, read the claims out. -/
def accept (s : String) : Option GoogleClaims :=
  match Specs.JSON.parseBytes (bytes s) with
  | some j => if IsToken google j then some (GoogleClaims.ofJSON j) else none
  | none => none

/-! ## Accepted tokens -/

/-- A realistic Google ID token payload, claims in Google's usual order,
    including claims outside the schema (`name`, `picture`, ...). -/
def realistic : String :=
  "{\"iss\":\"https://accounts.google.com\",\"azp\":\"407408718192.apps.googleusercontent.com\"," ++
  "\"aud\":\"407408718192.apps.googleusercontent.com\",\"sub\":\"110169484474386276334\"," ++
  "\"hd\":\"example.com\",\"email\":\"jsmith@example.com\",\"email_verified\":true," ++
  "\"at_hash\":\"HK6E_P6Dh8Y93mRNtsDB1Q\",\"nonce\":\"0394852-3190485-2490358\"," ++
  "\"name\":\"John Smith\",\"picture\":\"https://lh3.googleusercontent.com/a/photo\"," ++
  "\"given_name\":\"John\",\"family_name\":\"Smith\",\"locale\":\"en\"," ++
  "\"iat\":1353601026,\"exp\":1353604926}"

example : (accept realistic).isSome = true := by native_decide

example : (accept realistic).map (·.iss) = some (some (bytes "https://accounts.google.com")) := by
  native_decide
example : (accept realistic).map (·.sub) = some (some (bytes "110169484474386276334")) := by
  native_decide
example : (accept realistic).map (·.emailVerified) = some (some true) := by native_decide
example : (accept realistic).map (·.iat) = some (some (false, [1, 3, 5, 3, 6, 0, 1, 0, 2, 6])) := by
  native_decide
example : (accept realistic).map (·.nonce) = some (some (bytes "0394852-3190485-2490358")) := by
  native_decide

-- the same claims in another order, with whitespace, give the same extraction
example :
    accept " { \"exp\" : 1353604926 ,\n \"sub\":\"110169484474386276334\", \"iss\":\"https://accounts.google.com\" } "
      = accept "{\"iss\":\"https://accounts.google.com\",\"sub\":\"110169484474386276334\",\"exp\":1353604926}" := by
  native_decide

-- nothing is required: the empty object is a token with no claims
example : accept "{}" = some (GoogleClaims.ofJSON (.obj [])) := by native_decide
example : (accept "{}").map (·.sub) = some none := by native_decide

-- unknown claims may be any scalar, including numbers with fractions, null,
-- non-ASCII and escaped strings
example : (accept "{\"score\":1.5e3,\"x\":null,\"name\":\"Jos\\u00e9 \\\"J\\\" Ré\"}").isSome = true := by
  native_decide

-- known string claims may use escapes as long as they decode to ASCII
example : (accept "{\"sub\":\"\\u0031\\u0032\"}").map (·.sub) = some (some (bytes "12")) := by
  native_decide

-- integers keep their sign and digits; `0` is `[0]`
example : (accept "{\"iat\":-0}").map (·.iat) = some (some (true, [0])) := by native_decide

-- caps at the boundary: a 32-byte `sub`, a 12-digit `exp`
example : (accept ("{\"sub\":\"" ++ String.mk (List.replicate 32 '7') ++ "\"}")).isSome = true := by
  native_decide
example : (accept "{\"exp\":123456789012}").isSome = true := by native_decide

-- exactly `maxMembers` members
example : (accept ("{" ++ ",".intercalate ((List.range 32).map fun i => s!"\"k{i}\":{i}") ++ "}")).isSome
    = true := by native_decide

/-! ## Rejected inputs -/

-- not an object
example : (accept "[1,2]").isSome = false := by native_decide
example : (accept "\"iss\"").isSome = false := by native_decide

-- a known claim with the wrong type
example : (accept "{\"sub\":123}").isSome = false := by native_decide
example : (accept "{\"iat\":\"1353601026\"}").isSome = false := by native_decide
example : (accept "{\"email_verified\":\"true\"}").isSome = false := by native_decide

-- a known integer claim with a fraction or an exponent
example : (accept "{\"iat\":1353601026.0}").isSome = false := by native_decide
example : (accept "{\"exp\":1e9}").isSome = false := by native_decide

-- over the caps: a 33-byte `sub`, a 13-digit `iat`, a non-ASCII `hd`
example : (accept ("{\"sub\":\"" ++ String.mk (List.replicate 33 '7') ++ "\"}")).isSome = false := by
  native_decide
example : (accept "{\"iat\":1234567890123}").isSome = false := by native_decide
example : (accept "{\"hd\":\"exámple.com\"}").isSome = false := by native_decide
example : (accept "{\"hd\":\"ex\\u00e1mple.com\"}").isSome = false := by native_decide

-- a duplicated known claim
example : (accept "{\"sub\":\"1\",\"sub\":\"2\"}").isSome = false := by native_decide

-- an unknown claim that is not a scalar
example : (accept "{\"profile\":{\"name\":\"x\"}}").isSome = false := by native_decide
example : (accept "{\"scopes\":[\"a\"]}").isSome = false := by native_decide

-- too many members: `maxMembers + 1`
example : (accept ("{" ++ ",".intercalate ((List.range 33).map fun i => s!"\"k{i}\":{i}") ++ "}")).isSome
    = false := by native_decide

-- malformed JSON
example : (accept "{\"sub\":\"1\",}").isSome = false := by native_decide
example : (accept "{\"sub\":\"1\"").isSome = false := by native_decide

/-! ## Encoding -/

example : (encodeOutput (GoogleClaims.ofJSON (.obj []))).sub.present = 0 := by native_decide
example :
    ((accept realistic).map fun c => (encodeOutput c).iat) =
      some ⟨1, 0, 10, padTo [1, 3, 5, 3, 6, 0, 1, 0, 2, 6] timeMax⟩ := by native_decide
example :
    ((accept realistic).map fun c => (encodeOutput c).emailVerified) = some ⟨1, 1⟩ := by native_decide
example :
    ((accept realistic).map fun c => (encodeOutput c).hd.len) = some 11 := by native_decide

end Specs.JSONExtract.Tests
