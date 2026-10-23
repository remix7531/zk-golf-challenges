import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.Mul

/-!
# The two row shapes every per-position gadget uses (`JSONExtract`)

`mul` is a witnessed product (one `Mul` subcircuit) and `freeze` is the
register update `next = prev + active · (new − prev)` (one witnessed product
and one linear row).  They live here, below every gadget of one position, so
that each gadget can use them without depending on `Step`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

namespace Rows

/-- A circuit expression over the circom field. -/
abbrev E := Expression (F circomPrime)

/-- Witnessed product. -/
def mul (a b : E) : Circuit (F circomPrime) E := Mul.circuit { a := a, b := b }

/-- Pin `next = prev + active · (new - prev)`. -/
def freeze (active prev new next : E) : Circuit (F circomPrime) Unit := do
  let d ← mul active (new - prev)
  assertZero (next - prev - d)

end Rows
end Solution.JSONExtract
