import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.OneHot

/-!
# The `OneHot` gadget's bundled interface (`JSONExtract`)

`ohOf n x` is the `n`-wide one-hot indicator of a field element at the value
level, and the lemmas below expose `OneHot.circuit`'s `Assumptions` / `Spec` /
`localLength` / `output` as `rfl` lemmas, so a caller never unfolds its `main`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

/-- The `n`-wide one-hot indicator of a field value. -/
def ohOf (n : ℕ) (x : F circomPrime) : Vector (F circomPrime) n :=
  Vector.ofFn fun i : Fin n => if i.val = x.val then 1 else 0

@[simp] lemma oneHot_Assumptions (n : ℕ) [NeZero n] (inp : OneHot.Inputs (F circomPrime)) :
    (OneHot.circuit n).Assumptions inp = (n < 2 ^ 64 ∧ inp.x.val < n) := rfl

@[simp] lemma oneHot_localLength (n : ℕ) [NeZero n] (inp : Var OneHot.Inputs (F circomPrime)) :
    (OneHot.circuit n).localLength inp = n := rfl

@[simp] lemma oneHot_output (n : ℕ) [NeZero n] (inp : Var OneHot.Inputs (F circomPrime)) (k : ℕ) :
    (OneHot.circuit n).output inp k = varFromOffset (fields n) k := rfl

@[simp] lemma oneHot_channelsWithRequirements (n : ℕ) [NeZero n] :
    (OneHot.circuit n).channelsWithRequirements = [] := rfl

/-- The one-hot gadget returns exactly the indicator of its (in-range) input. -/
@[simp] lemma oneHot_Spec_iff (n : ℕ) [NeZero n] (inp : OneHot.Inputs (F circomPrime))
    (flags : fields n (F circomPrime)) :
    (OneHot.circuit n).Spec inp flags ↔ inp.x.val < n ∧ flags = ohOf n inp.x := by
  simp only [show (OneHot.circuit n).Spec = OneHot.Spec n from rfl, OneHot.Spec, ohOf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Vector.ext fun i hi => ?_⟩
    have := h2 ⟨i, hi⟩
    simpa using this
  · rintro ⟨h1, rfl⟩
    exact ⟨h1, fun i => by simp⟩

end Solution.JSONExtract
