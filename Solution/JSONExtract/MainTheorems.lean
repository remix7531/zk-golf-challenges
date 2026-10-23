import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.Model
import Solution.JSONExtract.Witness
import Solution.JSONExtract.Step

/-!
# Helpers for the top-level circuit (`JSONExtract`)

Slicing of the position-major register vectors `main` witnesses, and the
sums over the per-position signals. Supporting lemmas for the obligations of
`Main.lean` go here as well.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Witness (slots)

abbrev E := Expression (F circomPrime)

/-- The `n`-vector of position `i` in a position-major flattened register. -/
def sliceAt (n : ℕ) (v : Vector E (n * slots)) (i : ℕ) (hi : i < slots) : Vector E n :=
  Vector.ofFn fun s : Fin n => v[i * n + s.val]'(by
    have := s.isLt; have := hi
    calc i * n + s.val < i * n + n := by omega
      _ = (i + 1) * n := by ring
      _ ≤ slots * n := Nat.mul_le_mul_right n hi
      _ = n * slots := Nat.mul_comm _ _)

/-- Entry `i` of a per-slot register (the state before position `i`). -/
def prevAt (v : Vector E slots) (i : Fin bufferLen) : E :=
  v[i.val]'(by have := i.isLt; simp only [slots]; omega)

/-- Entry `i + 1` of a per-slot register (the state after position `i`). -/
def nextAt (v : Vector E slots) (i : Fin bufferLen) : E :=
  v[i.val + 1]'(by have := i.isLt; simp only [slots]; omega)

/-- The sum over the positions of one per-position signal. -/
def sumOver (sigs : Vector (Var Step.Outputs (F circomPrime)) bufferLen)
    (f : Var Step.Outputs (F circomPrime) → E) : E :=
  Fin.foldl bufferLen (fun acc i => acc + f sigs[i]) 0

end Solution.JSONExtract
