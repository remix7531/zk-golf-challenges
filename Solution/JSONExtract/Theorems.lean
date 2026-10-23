import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.LenFlagsTheorems
import Mathlib.Tactic.LinearCombination
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Mul

/-!
# Lemmas shared by the `JSONExtract` gadgets

Two families:

* the `Fin.foldl (· + f ·) 0` summations the gadgets use to write affine sums
  (both at the value level and under `Expression.eval`), and
* the small `rfl` lemmas that expose the `Mul` gadget's bundled interface
  (`Assumptions`, `Spec`, `localLength`, `output`) without unfolding its `main`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

/-- A left fold of additions over `Fin n` is the `Finset` sum. -/
lemma foldl_add_eq_sum {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) :
    Fin.foldl n (fun acc i => acc + f i) 0 = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc, ih (fun i => f i.castSucc)]

/-- `Expression.eval` distributes over a `Fin.foldl` summation of expressions. -/
lemma eval_foldl_sum {n : ℕ} (env : Environment (F circomPrime))
    (g : Fin n → Expression (F circomPrime)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) 0) =
      ∑ i : Fin n, Expression.eval env (g i) :=
  LenFlags.eval_foldl_sum env g


/-- `Expression.eval` distributes over a filtered `List.foldl` summation. -/
lemma eval_list_foldl_ite {α : Type*} (env : Environment (F circomPrime)) (c : α → Prop)
    [DecidablePred c] (g : α → Expression (F circomPrime)) (l : List α)
    (init : Expression (F circomPrime)) :
    Expression.eval env (l.foldl (fun acc e => if c e then acc + g e else acc) init) =
      l.foldl (fun acc e => if c e then acc + Expression.eval env (g e) else acc)
        (Expression.eval env init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases h : c a <;> simp only [h, if_true, if_false, Expression.eval, reduceIte]

/-- `Expression.eval` distributes over a filtered `Fin.foldl` summation. -/
lemma eval_foldl_ite {n : ℕ} (env : Environment (F circomPrime)) (c : Fin n → Prop)
    [DecidablePred c] (g : Fin n → Expression (F circomPrime)) :
    Expression.eval env (Fin.foldl n (fun acc e => if c e then acc + g e else acc) 0) =
      Fin.foldl n (fun acc e => if c e then acc + Expression.eval env (g e) else acc) 0 := by
  induction n with
  | zero => simp only [Fin.foldl_zero]; rfl
  | succ m ih =>
    have key : Expression.eval env
        (Fin.foldl m (fun (acc : Expression (F circomPrime)) (i : Fin m) =>
          if c i.castSucc then acc + g i.castSucc else acc) 0)
        = Fin.foldl m (fun (acc : F circomPrime) (i : Fin m) =>
          if c i.castSucc then acc + Expression.eval env (g i.castSucc) else acc) 0 :=
      ih (fun i => c i.castSucc) (fun i => g i.castSucc)
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    by_cases h : c (Fin.last m) <;> simp only [h, if_true, if_false, Expression.eval, key]

/-! ## Channel-freeness

No gadget in this solution interacts with a channel, so the
`requirementsChannelsLawful` obligation is vacuous. Its default tactic proves
that by unfolding `main` and normalizing with `circuit_norm`, which is hopeless
on the larger gadgets (`ByteClass`, `Step`, the slot pins): the operation list is
hundreds of entries long. The two facts below are all the obligation needs, and
both hold by `rfl` -- kernel reduction of the concrete operation list is cheap,
it is the `simp` traversal that is not. -/

open Challenge.Instances.JSONExtract.Interface in
theorem requirementsChannelsLawful_of_noChannels
    {ops : Operations (F circomPrime)} {guarantees : List (RawChannel (F circomPrime))}
    (hsub : ops.subcircuitChannelsWithRequirements = [])
    (hint : ops.shallowInteractions = []) :
    ops.RequirementsChannelsLawful guarantees [] := by
  refine ⟨by rw [hsub]; exact List.Subset.refl _, ?_, ?_⟩
  · intro c hc
    rw [Operations.shallowChannels_eq_interactions_map, hint] at hc
    simp at hc
  · intro env _
    rw [Operations.inChannelsOrRequirements_iff_forall_mem]
    intro i hi
    rw [hint] at hi
    simp at hi

/-- The indicator vector of an `Option` state: all-zero for a rejection. -/
def optInd {n : ℕ} (o : Option (Fin n)) (j : Fin n) : F circomPrime :=
  if o = some j then 1 else 0

@[simp] lemma optInd_none {n : ℕ} (j : Fin n) : optInd (none : Option (Fin n)) j = 0 := rfl

lemma optInd_some {n : ℕ} (d j : Fin n) :
    optInd (some d) j = if d = j then 1 else 0 := by
  simp only [optInd, Option.some.injEq]

namespace Mul

@[simp] lemma circuit_Assumptions (x : Inputs (F circomPrime)) :
    circuit.Assumptions x = True := rfl

@[simp] lemma circuit_Spec (x : Inputs (F circomPrime)) (o : F circomPrime) :
    circuit.Spec x o = (o = x.a * x.b) := rfl

@[simp] lemma circuit_localLength (x : Var Inputs (F circomPrime)) :
    circuit.localLength x = 1 := rfl

@[simp] lemma circuit_output (x : Var Inputs (F circomPrime)) (k : ℕ) :
    circuit.output x k = var ⟨k⟩ := rfl

@[simp] lemma circuit_channelsWithRequirements :
    circuit.channelsWithRequirements = [] := rfl

end Mul

open Circomlib in
/-- `IsEqual` has no precondition. -/
@[simp] lemma isEqual_Assumptions (x : fieldPair (F circomPrime)) :
    (IsEqual.circuit (p := circomPrime)).Assumptions x = True := rfl

open Circomlib in
/-- `IsEqual`'s postcondition, without unfolding its implementation. -/
@[simp] lemma isEqual_Spec (x : fieldPair (F circomPrime)) (o : F circomPrime) :
    (IsEqual.circuit (p := circomPrime)).Spec x o = (o = if x.1 = x.2 then 1 else 0) := rfl

open Circomlib in
@[simp] lemma isEqual_localLength (x : Var fieldPair (F circomPrime)) :
    (IsEqual.circuit (p := circomPrime)).localLength x = 2 := rfl

open Circomlib in
@[simp] lemma isEqual_output (x : Var fieldPair (F circomPrime)) (k : ℕ) :
    (IsEqual.circuit (p := circomPrime)).output x k = var ⟨k + 1⟩ := rfl

open Circomlib in
@[simp] lemma isEqual_channelsWithRequirements :
    (IsEqual.circuit (p := circomPrime)).channelsWithRequirements = [] := rfl

end Solution.JSONExtract
