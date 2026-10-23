import Challenge.Specs.Parser

/-!
Test vectors for the parser-combinator library. Inputs are byte lists written
as `List ℕ`; `native_decide` evaluates the parsers.
-/

namespace Specs.Parser.Tests

open Specs.Parser

/-- ASCII digit test. -/
def isDigit (c : ℕ) : Bool := 0x30 ≤ c && c ≤ 0x39

/-! ## Primitives -/

example : satisfy isDigit [0x31, 0x61] = some (0x31, [0x61]) := by native_decide
example : satisfy isDigit [0x61] = none := by native_decide
example : satisfy isDigit [] = none := by native_decide
example : byte 0x7B [0x7B, 0x7D] = some ((), [0x7D]) := by native_decide
example : byte 0x7B [0x7D] = none := by native_decide
example : eof ([] : List ℕ) = some ((), []) := by native_decide
example : eof [0x20] = none := by native_decide
example : notFollowedBy isDigit [0x61] = some ((), [0x61]) := by native_decide
example : notFollowedBy isDigit [0x31] = none := by native_decide
example : notFollowedBy isDigit [] = some ((), []) := by native_decide
example : skipWhile (· == 0x20) [0x20, 0x20, 0x61] = some ((), [0x61]) := by native_decide

/-! ## Sequencing and choice -/

example : (byte 0x7B *> satisfy isDigit) [0x7B, 0x35, 0x7D] = some (0x35, [0x7D]) := by
  native_decide
example : (satisfy isDigit <* byte 0x7D) [0x35, 0x7D] = some (0x35, []) := by native_decide
example : (satisfy isDigit <* byte 0x7D) [0x35, 0x2C] = none := by native_decide
example : ((fun c => c - 0x30) <$> satisfy isDigit) [0x37] = some (7, []) := by native_decide
example : (byte 0x2D <|> byte 0x2B) [0x2B] = some ((), []) := by native_decide
example : (byte 0x2D <|> byte 0x2B) [0x2A] = none := by native_decide
example : optional (byte 0x2D) [0x2D, 0x31] = some (some (), [0x31]) := by native_decide
example : optional (byte 0x2D) [0x31] = some (none, [0x31]) := by native_decide

/-! ## Bounded repetition -/

-- takes the maximal digit run
example : manyUpTo 5 (satisfy isDigit) [0x31, 0x32, 0x33, 0x61] =
    some ([0x31, 0x32, 0x33], [0x61]) := by native_decide
-- stops at the bound, leaving the rest
example : manyUpTo 2 (satisfy isDigit) [0x31, 0x32, 0x33, 0x61] =
    some ([0x31, 0x32], [0x33, 0x61]) := by native_decide
-- never fails
example : manyUpTo 3 (satisfy isDigit) [0x61] = some ([], [0x61]) := by native_decide
example : manyUpTo 0 (satisfy isDigit) [0x31] = some ([], [0x31]) := by native_decide

-- separated items: `1,2,3`
example : sepByUpTo 8 (satisfy isDigit) (byte 0x2C) [0x31, 0x2C, 0x32, 0x2C, 0x33, 0x5D] =
    some ([0x31, 0x32, 0x33], [0x5D]) := by native_decide
-- empty list
example : sepByUpTo 8 (satisfy isDigit) (byte 0x2C) [0x5D] = some ([], [0x5D]) := by native_decide
-- committed after a separator: `1,]` stops BEFORE the comma
example : sepByUpTo 8 (satisfy isDigit) (byte 0x2C) [0x31, 0x2C, 0x5D] =
    some ([0x31], [0x2C, 0x5D]) := by native_decide
-- the item cap: a third item is left unparsed together with its separator
example : sepByUpTo 2 (satisfy isDigit) (byte 0x2C) [0x31, 0x2C, 0x32, 0x2C, 0x33] =
    some ([0x31, 0x32], [0x2C, 0x33]) := by native_decide
example : sepByUpTo 0 (satisfy isDigit) (byte 0x2C) [0x31] = some ([], [0x31]) := by native_decide

end Specs.Parser.Tests
