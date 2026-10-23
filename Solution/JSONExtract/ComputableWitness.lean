import Solution.JSONExtract.Step
import Solution.JSONExtract.Witgen
import Solution.JSONExtract.Anchors
import Solution.JSONExtract.Acceptance
import Solution.JSONExtract.SlotPins
import Solution.JSONExtract.LenFlags
import Challenge.Utils.ComputableWitnessLemmas

/-!
# `computableWitness` for `JSONExtract`, gadget by gadget

Every witness generator of the solution is a witness-IR program whose value is
determined by the circuit input together with the cells allocated before it.
This file proves that, bottom-up, in the same layout as `Cost.lean`: one section
per gadget, each exporting `computableWitnesses` for the gadget's bundle, up to
and including `Step.computableWitnesses` (one position of the automaton).

The currency is `CW.Stable n₀ pin e`: two prover environments that agree below
`n₀` and give the parent input `pin` the same value give `e` the same value.  A
gadget's own input expressions are `Stable` at every offset; a cell allocated by
an earlier child at index `j` is `Stable` at any `n₀ > j`.  `cw_peel` splits a
gadget's `main` into its children (keyed on the circuit former, never on the
operation list), `stableP_tac` discharges a child's input agreement, and
`stable_tac` walks an expression's `+`/`-`/`*` structure.

`IRAgree` is the toolkit for `Main`'s own witness sites, whose generators are
the unrolled witness-IR programs of `Witgen.lean`: `UAgree`/`FAgree`/`BAgree`/
`VAgree` say that two environments give an IR expression the same value whatever
the locals are, they are closed under every former the programs use, and
`evalSteps_congr`/`eval_ir_congr` lift that to a whole program.  `stepBlock_agree`
walks a position block and `runSteps_agree` the whole unrolled run, so each of
`Main`'s eleven witness sites has its own agreement lemma (`stIR_agree`, ...,
`outIR_agree`, `lenFlagsOut_eval_agree`, `accmOut_eval_agree`).
-/
namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Circomlib

-- the `ProvableStruct` normalisation of a wide input struct (the byte classifier's
-- 44 flags) recurses deeper than the default budget
set_option maxRecDepth 8000

namespace CW

/-! ## Names for the toolkit -/

/-- The toolkit's structural computable-witness predicate on nested operations. -/
abbrev SCW {P : TypeMap} [CircuitType P] (pin : Var P (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime)) (offset : ℕ)
    (ops : Operations (F circomPrime)) : Prop :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses
    pin env env' offset ops

/-- The toolkit's structural computable-witness predicate on flat operations. -/
abbrev FSCW {P : TypeMap} [CircuitType P] (pin : Var P (F circomPrime))
    (env env' : ProverEnvironment (F circomPrime)) (offset : ℕ)
    (ops : List (FlatOperation (F circomPrime))) : Prop :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.StructuralComputableWitnesses
    pin env env' offset ops

alias bind_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff
alias pure_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff
alias witnessVar_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVar_structuralComputableWitnesses_iff
alias witnessField_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff
alias witnessVector_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff
alias witnessIR_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessIR_structuralComputableWitnesses_iff
alias assertZero_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff
alias forEach_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff
alias foldlRange_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.foldlRange_structuralComputableWitnesses_iff
/-- Peeling lemma for `Circuit.map`, which the toolkit does not cover. -/
@[circuit_norm]
theorem map_iff {α β : Type} {P : TypeMap} [Inhabited α] [CircuitType P] {m n : ℕ}
    (pin : Var P (F circomPrime)) (xs : Vector α m) (body : α → Circuit (F circomPrime) β)
    (constant : Circuit.ConstantLength body) (env env' : ProverEnvironment (F circomPrime)) :
    SCW pin env env' n ((Circuit.map xs body constant).operations n) ↔
      ∀ i : Fin m, SCW pin env env' (n + i.val * (body default).localLength)
        ((body xs[i.val]).operations (n + i.val * (body default).localLength)) := by
  unfold SCW
  rw [Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.structuralComputableWitnesses_iff_forAll]
  rw [Circuit.map.forAll]
  simp_rw [← Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.structuralComputableWitnesses_iff_forAll
    pin env env']

alias mapFinRange_iff :=
  Challenge.Utils.ComputableWitnessLemmas.Circuit.mapFinRange_structuralComputableWitnesses_iff
alias subcircuit_iff :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff
alias assertion_iff :=
  Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff
alias forAllFlat_of :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
alias flatOfSubcircuit :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
alias flatOfSubcircuit' :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
alias flatOfGeneral :=
  Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses
alias flatOfGeneral' :=
  Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
alias flatOfAssertion :=
  Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses
alias flatOfAssertion' :=
  Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_flatStructuralComputableWitnesses_of_condition

/-- `witness` at type `field` is `Circuit.witnessField`. -/
theorem witness_field_eq (c : Witgen.FExpr (F circomPrime)) :
    (witness c : Circuit (F circomPrime) (Expression (F circomPrime)))
      = Circuit.witnessField c :=
  rfl

/-- `AgreesBelow` as a rewriting rule with an explicit index. -/
theorem agreesBelow_get {env env' : ProverEnvironment (F circomPrime)} {N : ℕ}
    (h : env.AgreesBelow N env') (i : ℕ) (hi : i < N) : env.get i = env'.get i := h i hi

/-! ## The bridge to the trusted statement -/

/-- Turn the toolkit's structural predicate into the trusted
`Circuit.ComputableWitnesses`.  The only extra input is that the circuit's own
input is read below the starting offset, which is exactly the hypothesis the
trusted `computableWitness` statement hands us. -/
theorem computableWitnesses_of_structural {P : TypeMap} [ProvableType P] {α : Type}
    (pin : Var P (F circomPrime)) (c : Circuit (F circomPrime) α) (n : ℕ)
    (hinput : ProverEnvironment.OnlyAccessedBelow n
      (fun env : ProverEnvironment (F circomPrime) => eval env pin))
    (h : ∀ env env', SCW pin env env' n (c.operations n)) :
    Circuit.ComputableWitnesses c n := by
  intro env env'
  change (c.operations n).forAllFlat n
    { witness := fun k _ compute => env.AgreesBelow k env' → compute.eval env = compute.eval env' }
  have hflat := forAllFlat_of pin env env' (h env env')
  unfold Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition at hflat
  rw [← Operations.forAll_toFlat_iff] at hflat ⊢
  apply FlatOperation.forAll_implies (F := F circomPrime) n ?_ hflat
  have himplies : ∀ (ops : List (FlatOperation (F circomPrime))) (off : ℕ),
      n ≤ off →
      FlatOperation.forAll off
        (Condition.implies
          (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
            pin env env')
          { witness := fun k _ compute =>
              env.AgreesBelow k env' → compute.eval env = compute.eval env' }).ignoreSubcircuit
        ops := by
    intro ops off hoff
    induction ops generalizing off with
    | nil => simp [FlatOperation.forAll]
    | cons op ops ih =>
      cases op with
      | witness m compute =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          refine ⟨?_, ih (m + off) (by omega)⟩
          intro hparent hagree
          exact hparent hagree
            (hinput env env' (ProverEnvironment.agreesBelow_of_le hagree hoff))
      | assert e =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | lookup l =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
      | interact i =>
          simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
          exact ⟨by intro _; trivial, ih off hoff⟩
  exact himplies ((c.operations n).toFlat) n (le_refl n)

/-- Pointwise implication of two conditions, as the `forAll_implies` premise.
Comparing the two conditions here (rather than letting the unifier equate two whole
`forAllFlat` applications) keeps the check at the level of a single witness row:
the unifier never walks the operation list of the circuit. -/
theorem forAll_implies_of_witness {c c' : Condition (F circomPrime)}
    (hw : ∀ (n m : ℕ) (compute : Witgen.WitgenIR (F circomPrime) m),
      c.witness n m compute → c'.witness n m compute)
    (ha : ∀ (n : ℕ) (e : Expression (F circomPrime)), c.assert n e → c'.assert n e)
    (hl : ∀ (n : ℕ) (l : Lookup (F circomPrime)), c.lookup n l → c'.lookup n l)
    (hi : ∀ (n : ℕ) (i : AbstractInteraction (F circomPrime)), c.interact n i → c'.interact n i) :
    ∀ (ops : List (FlatOperation (F circomPrime))) (n : ℕ),
      FlatOperation.forAll n (c.implies c').ignoreSubcircuit ops := by
  intro ops
  induction ops with
  | nil => intro n; simp [FlatOperation.forAll]
  | cons op ops ih =>
    intro n
    cases op with
    | witness m compute =>
        exact ⟨hw n m compute, ih (m + n)⟩
    | assert e => exact ⟨ha n e, ih n⟩
    | lookup l => exact ⟨hl n l, ih n⟩
    | interact i => exact ⟨hi n i, ih n⟩

/-- Bundle-level bridge: the structural predicate on `circuit.main` gives clean's
`ComputableWitnesses`.  The two conditions are the same proposition, but they are
spelled differently, so the transport goes through `forAll_implies` rather than
through a defeq on the whole `forAllFlat` application. -/
theorem computableWitnesses_of_structural'' {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuitBase (F circomPrime) Input Output}
    (h : ∀ (n : ℕ) (input : Var Input (F circomPrime))
        (env env' : ProverEnvironment (F circomPrime)),
      SCW input env env' n ((circuit.main input).operations n)) :
    circuit.ComputableWitnesses := by
  intro n input env env'
  have hflat := forAllFlat_of input env env' (h n input env env')
  rw [← Operations.forAll_toFlat_iff] at hflat ⊢
  exact FlatOperation.forAll_implies n
    (forAll_implies_of_witness (fun _ _ _ hx => hx) (fun _ _ _ => trivial)
      (fun _ _ _ => trivial) (fun _ _ _ => trivial) _ n) hflat

theorem computableWitnesses_of_structural' {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuitBase (F circomPrime) Input Output}
    (main : Var Input (F circomPrime) → Circuit (F circomPrime) (Var Output (F circomPrime)))
    (hmain : circuit.main = main)
    (h : ∀ (n : ℕ) (input : Var Input (F circomPrime))
        (env env' : ProverEnvironment (F circomPrime)),
      SCW input env env' n ((main input).operations n)) :
    circuit.ComputableWitnesses := by
  subst hmain
  exact computableWitnesses_of_structural'' h

/-! ## Stability of an expression -/

/-- `e`'s value is determined by the parent input together with the cells below `n₀`. -/
def Stable {P : TypeMap} [CircuitType P] (n₀ : ℕ) (pin : Var P (F circomPrime))
    (e : Expression (F circomPrime)) : Prop :=
  ∀ env env' : ProverEnvironment (F circomPrime),
    env.AgreesBelow n₀ env' → eval env pin = eval env' pin →
      Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e

namespace Stable

variable {P : TypeMap} [CircuitType P] {n₀ n₁ : ℕ} {pin : Var P (F circomPrime)}
  {e f : Expression (F circomPrime)}

theorem mono (h : Stable n₀ pin e) (hle : n₀ ≤ n₁) : Stable n₁ pin e :=
  fun env env' h_agree h_input =>
    h env env' (ProverEnvironment.agreesBelow_of_le h_agree hle) h_input

theorem const (c : F circomPrime) : Stable n₀ pin (Expression.const c) :=
  fun _ _ _ _ => rfl

theorem add (h : Stable n₀ pin e) (h' : Stable n₀ pin f) : Stable n₀ pin (e + f) := by
  intro env env' ha hi
  show Expression.eval _ (Expression.add e f) = Expression.eval _ (Expression.add e f)
  simp only [Expression.eval, h env env' ha hi, h' env env' ha hi]

theorem mul (h : Stable n₀ pin e) (h' : Stable n₀ pin f) : Stable n₀ pin (e * f) := by
  intro env env' ha hi
  show Expression.eval _ (Expression.mul e f) = Expression.eval _ (Expression.mul e f)
  simp only [Expression.eval, h env env' ha hi, h' env env' ha hi]

theorem sub (h : Stable n₀ pin e) (h' : Stable n₀ pin f) : Stable n₀ pin (e - f) := by
  intro env env' ha hi
  simp only [eval_sub, h env env' ha hi, h' env env' ha hi]

theorem neg (h : Stable n₀ pin e) : Stable n₀ pin (-e) := by
  intro env env' ha hi
  simp only [eval_neg, h env env' ha hi]

/-- A cell allocated below `n₀`. -/
theorem var {j : ℕ} (hj : j < n₀) : Stable n₀ pin (Expression.var ⟨j⟩) := by
  intro env env' ha _
  exact ha j hj

theorem ite (c : Prop) [Decidable c] {a b : Expression (F circomPrime)}
    (ha : Stable n₀ pin a) (hb : Stable n₀ pin b) : Stable n₀ pin (if c then a else b) := by
  by_cases h : c
  · rwa [if_pos h]
  · rwa [if_neg h]

/-- Stability travels through a `Fin.foldl` whose step preserves it. -/
theorem finFoldl : ∀ (m : ℕ)
    (step : Expression (F circomPrime) → Fin m → Expression (F circomPrime))
    (init : Expression (F circomPrime)),
    Stable n₀ pin init →
    (∀ (acc : Expression (F circomPrime)) (i : Fin m),
      Stable n₀ pin acc → Stable n₀ pin (step acc i)) →
    Stable n₀ pin (Fin.foldl m step init)
  | 0, step, init, hinit, _ => hinit
  | m + 1, step, init, hinit, hstep => by
      rw [Fin.foldl_succ]
      exact finFoldl m (fun acc i => step acc i.succ) (step init 0)
        (hstep init 0 hinit) (fun acc i h => hstep acc i.succ h)

end Stable


/-- Stability of an expression that reads the parent input through a function. -/
theorem Stable.of_eval {P : TypeMap} [CircuitType P] {n : ℕ} {pin : Var P (F circomPrime)}
    {e : Expression (F circomPrime)} (f : CircuitType.ProverValue P (F circomPrime) → F circomPrime)
    (hf : ∀ env : ProverEnvironment (F circomPrime),
      Expression.eval env.toEnvironment e = f (eval env pin)) :
    Stable n pin e := by
  intro env env' _ hp
  rw [hf env, hf env', hp]

/-- A cell of a `varFromOffset` block allocated below `n₀`. -/
theorem Stable.getElem_varFromOffset {P : TypeMap} [CircuitType P] {pin : Var P (F circomPrime)}
    {m off j n₀ : ℕ} (hj : j < m) (h : off + j < n₀) :
    Stable n₀ pin ((varFromOffset (fields m) off : Var (fields m) (F circomPrime))[j]'hj) := by
  rw [ProvableType.varFromOffset_fields]
  simp only [Vector.getElem_mapRange]
  exact Stable.var h

/-- Every cell of `v` is `Stable`. -/
def StableV {P : TypeMap} [CircuitType P] (n₀ : ℕ) (pin : Var P (F circomPrime)) {m : ℕ}
    (v : Vector (Expression (F circomPrime)) m) : Prop :=
  ∀ (j : ℕ) (hj : j < m), Stable n₀ pin (v[j]'hj)

namespace StableV

variable {P : TypeMap} [CircuitType P] {n₀ n₁ m : ℕ} {pin : Var P (F circomPrime)}
  {v : Vector (Expression (F circomPrime)) m}

theorem mono (h : StableV n₀ pin v) (hle : n₀ ≤ n₁) : StableV n₁ pin v :=
  fun j hj => (h j hj).mono hle

theorem getElem (h : StableV n₀ pin v) (j : ℕ) (hj : j < m) : Stable n₀ pin (v[j]'hj) := h j hj

theorem getElem_fin (h : StableV n₀ pin v) (j : Fin m) : Stable n₀ pin v[j] := h j.val j.isLt

end StableV

/-- `Stable` as a rewriting step on an evaluation goal. -/
theorem Stable.apply {P : TypeMap} [CircuitType P] {n : ℕ} {pin : Var P (F circomPrime)}
    {e : Expression (F circomPrime)} (h : Stable n pin e)
    (env env' : ProverEnvironment (F circomPrime)) (ha : env.AgreesBelow n env')
    (hp : eval env pin = eval env' pin) :
    Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e :=
  h env env' ha hp

/-- `Stable.of_eval` with the parent value abstracted, so a tactic can read the
witnessing function `f` off the goal by higher-order unification. -/
theorem Stable.of_eval_gen {P : TypeMap} [CircuitType P] {n : ℕ} {pin : Var P (F circomPrime)}
    {e : Expression (F circomPrime)}
    (f : CircuitType.ProverValue P (F circomPrime) → F circomPrime)
    (hf : ∀ (env : ProverEnvironment (F circomPrime))
        (v : CircuitType.ProverValue P (F circomPrime)),
      eval env pin = v → Expression.eval env.toEnvironment e = f v) :
    Stable n pin e := by
  intro env env' _ hp
  rw [hf env _ rfl, hf env' _ rfl, hp]

/-- Stability of an expression that is a projection of the gadget's own input. -/
syntax "stable_input_tac" : tactic
macro_rules
  | `(tactic| stable_input_tac) => `(tactic|
      (refine CW.Stable.of_eval_gen ?f ?hf
       case hf =>
         intro envX vX hvX
         simp only [circuit_norm] at hvX ⊢
         rw [hvX]))

/-- Discharge a `Stable` goal: walk the expression's `+`, `-`, `*` structure, then
close each leaf with a constant, an already-allocated cell, or one of the
gadget's own input-stability hypotheses. -/
syntax "stable_tac" : tactic
macro_rules
  | `(tactic| stable_tac) => `(tactic|
      repeat' first
        | apply CW.Stable.add
        | apply CW.Stable.sub
        | apply CW.Stable.mul
        | apply CW.Stable.neg
        | apply CW.Stable.ite
        | exact CW.Stable.const _
        | exact CW.Stable.var (by omega)
        | apply_assumption
        | simp only [SubAutomaton.mass, MainAutomaton.plainMass, MainAutomaton.gatedMass,
            RouteSlot.ofsAt, Vector.getElem_mapIdx, Vector.getElem_mapRange,
            Vector.getElem_mapFinRange, ProvableType.varFromOffset_fields, Fin.getElem_fin,
            matcher_output, oneHot_output, routeSlot_output, lessThan_output,
            Mul.circuit_output, isEqual_output]
        | (refine CW.Stable.finFoldl _ _ _ ?_ fun acc i hacc => ?_)
        | omega)

/-- Discharge the `hinput` obligation of a child gadget whose input is a struct
literal: split the struct into its components and close each with `stable_tac`. -/
syntax "stableP_tac" : tactic
macro_rules
  | `(tactic| stableP_tac) => `(tactic|
      (intro envA envB hagree hp
       have hp' := hp
       try simp only [CircuitType.eval_expression_prover_to_verifier,
         ProvableStruct.eval_eq_eval] at hp
       simp only [circuit_norm, Prod.mk.injEq]
       and_intros <;>
         repeat' first
           | with_reducible rfl
           | rw [hp]
           | exact hagree _ (by omega)
           | refine congrArg₂ (· + ·) ?_ ?_
           | refine congrArg₂ (· - ·) ?_ ?_
           | refine congrArg₂ (· * ·) ?_ ?_
           | (refine CW.Stable.apply ?_ envA envB hagree hp'
              stable_tac)
           | (apply Vector.ext
              intro j hj
              simp only [Vector.getElem_map, Vector.getElem_mapRange,
                Vector.getElem_mapFinRange, ProvableType.varFromOffset_fields,
                Expression.eval])
           | (simp only [Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true]
              and_intros)))

/-! ## Offset-tolerant subcircuit wrappers

The toolkit's subcircuit lemmas identify the *structural* offset with the
subcircuit's own offset.  A peel produces the two in different but equal
spellings, and letting the unifier reconcile them forces a `whnf` of the child
circuit.  These wrappers take the two offsets separately with their equality, so
every match stays first-order, and they take the child's input agreement in the
`Stable` currency. -/

theorem flat_subcircuit {P Input Output : TypeMap}
    [CircuitType P] [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit (F circomPrime) Input Output)
    (pin : Var P (F circomPrime)) (input : Var Input (F circomPrime))
    (n m : ℕ) (hnm : m = n)
    (hinput : ∀ env env' : ProverEnvironment (F circomPrime),
      env.AgreesBelow m env' → eval env pin = eval env' pin → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses)
    (env env' : ProverEnvironment (F circomPrime)) :
    FSCW pin env env' n (circuit.toSubcircuit m input).ops.toFlat := by
  subst hnm
  refine flatOfSubcircuit' circuit pin input _ ?_ hcircuit env env'
  intro k e e' hle hagree hp
  exact hinput e e' (ProverEnvironment.agreesBelow_of_le hagree hle) hp

theorem flat_general {P Input Output : TypeMap}
    [CircuitType P] [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (F circomPrime) Input Output)
    (pin : Var P (F circomPrime)) (input : Var Input (F circomPrime))
    (n m : ℕ) (hnm : m = n)
    (hinput : ∀ env env' : ProverEnvironment (F circomPrime),
      env.AgreesBelow m env' → eval env pin = eval env' pin → eval env input = eval env' input)
    (hcircuit : circuit.base.ComputableWitnesses)
    (env env' : ProverEnvironment (F circomPrime)) :
    FSCW pin env env' n (circuit.toSubcircuit m input).ops.toFlat := by
  subst hnm
  refine flatOfGeneral' circuit pin input _ ?_ hcircuit env env'
  intro k e e' hle hagree hp
  exact hinput e e' (ProverEnvironment.agreesBelow_of_le hagree hle) hp

/-- An assertion child whose structural predicate is proved directly, with whatever
hypothesis the caller has, instead of through the child's `ComputableWitnesses`
(which forces the caller to show the child's whole input struct agrees). -/
theorem flat_assertion_of_structural {P Input : TypeMap} [CircuitType P] [ProvableType Input]
    (circuit : FormalAssertion (F circomPrime) Input) (pin : Var P (F circomPrime))
    (inp : Var Input (F circomPrime)) (n m : ℕ) (hnm : m = n)
    (env env' : ProverEnvironment (F circomPrime))
    (h : SCW pin env env' m ((circuit.main inp).operations m)) :
    FSCW pin env env' n (((circuit.main inp).operations m).toFlat) := by
  subst hnm
  unfold FSCW
  rw [Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.FlatOperation.structuralComputableWitnesses_iff_forAll,
    Operations.forAll_toFlat_iff]
  exact forAllFlat_of pin env env' h

theorem flat_assertion {P Input : TypeMap} [CircuitType P] [ProvableType Input]
    (circuit : FormalAssertion (F circomPrime) Input)
    (pin : Var P (F circomPrime)) (input : Var Input (F circomPrime))
    (n m : ℕ) (hnm : m = n)
    (hinput : ∀ env env' : ProverEnvironment (F circomPrime),
      env.AgreesBelow m env' → eval env pin = eval env' pin → eval env input = eval env' input)
    (hcircuit : circuit.ComputableWitnesses)
    (env env' : ProverEnvironment (F circomPrime)) :
    FSCW pin env env' n ((circuit.main input).operations m).toFlat := by
  subst hnm
  refine flatOfAssertion' circuit pin input _ ?_ hcircuit env env'
  intro k e e' hle hagree hp
  exact hinput e e' (ProverEnvironment.agreesBelow_of_le hagree hle) hp

/-- Peeling lemma for a `GeneralFormalCircuit` invoked through its `CoeFun`
(`subcircuitWithAssertion`), which the toolkit does not cover. -/
@[circuit_norm]
theorem subcircuitWithAssertion_iff {P Input Output : TypeMap}
    [CircuitType P] [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (F circomPrime) Input Output)
    (pin : Var P (F circomPrime)) (input : Var Input (F circomPrime)) (n : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    SCW pin env env' n ((subcircuitWithAssertion circuit input).operations n) ↔
      FSCW pin env env' n ((circuit.toSubcircuit n input).ops.toFlat) := by
  unfold subcircuitWithAssertion
  simp [Circuit.operations,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.StructuralComputableWitnesses]

/-! ## Subcircuit outputs

A child's output term is `(subcircuit c inp).output n`; rewriting it to
`(c.main inp).output n` lets the caller compute the concrete cell indices by
unfolding the child's `main` (its *operations* stay packaged in the subcircuit
node, so nothing of the child's interface is unfolded). -/

@[circuit_norm]
theorem sub_output_main {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : FormalCircuit (F circomPrime) Input Output) (inp : Var Input (F circomPrime)) (n : ℕ) :
    (subcircuit c inp).output n = (c.main inp).output n :=
  (c.elaborated.output_eq inp n).symm

@[circuit_norm]
theorem subWithAssertion_output_main {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (c : GeneralFormalCircuit (F circomPrime) Input Output) (inp : Var Input (F circomPrime))
    (n : ℕ) :
    (subcircuitWithAssertion c inp).output n = (c.main inp).output n :=
  (c.elaborated.output_eq inp n).symm

@[circuit_norm]
theorem sub_localLength {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : FormalCircuit (F circomPrime) Input Output) (inp : Var Input (F circomPrime)) (n : ℕ) :
    (subcircuit c inp).localLength n = c.localLength inp := rfl

@[circuit_norm]
theorem subWithAssertion_localLength {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (c : GeneralFormalCircuit (F circomPrime) Input Output) (inp : Var Input (F circomPrime))
    (n : ℕ) :
    (subcircuitWithAssertion c inp).localLength n = c.localLength inp := rfl

@[circuit_norm]
theorem assertion_localLength {Input : TypeMap} [ProvableType Input]
    (c : FormalAssertion (F circomPrime) Input) (inp : Var Input (F circomPrime)) (n : ℕ) :
    (assertion c inp).localLength n = c.localLength inp := rfl

/-! ## Witness-free operation lists

`===` (clean's `Gadgets.Equality`) and every assertion-only gadget emit no witness
row at all, so they are structurally computable wherever they sit. -/

theorem toFlat_append (a b : Operations (F circomPrime)) :
    (a ++ b).toFlat = a.toFlat ++ b.toFlat := by
  induction a using Operations.induct with
  | empty => simp [Operations.toFlat]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | interact _ _ ih =>
    simp [Operations.toFlat, ih]
  | subcircuit s _ ih => simp [Operations.toFlat, ih, List.append_assoc]

theorem toFlat_flatten (L : List (Operations (F circomPrime))) :
    Operations.toFlat L.flatten = (L.map Operations.toFlat).flatten := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatten_cons, toFlat_append, ih, List.map_cons, List.flatten_cons]

/-- A flat operation list without witnesses satisfies the structural
computable-witness condition at every offset. -/
theorem flatStructural_of_no_witness {P : TypeMap} [CircuitType P]
    (pin : Var P (F circomPrime)) (env env' : ProverEnvironment (F circomPrime)) :
    ∀ (ops : List (FlatOperation (F circomPrime))) (offset : ℕ),
      (∀ x ∈ ops, match x with | .witness _ _ => False | _ => True) →
      FSCW pin env env' offset ops := by
  intro ops
  induction ops with
  | nil => intro offset _; trivial
  | cons x rest ih =>
    intro offset h
    have h_rest : ∀ y ∈ rest, match y with | .witness _ _ => False | _ => True :=
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases x with
    | witness m c => exact absurd (h _ (List.mem_cons_self ..)) (by simp)
    | assert e => exact ih offset h_rest
    | lookup l => exact ih offset h_rest
    | interact i => exact ih offset h_rest

/-- The `Equality` assertion emits only `assertZero` rows. -/
theorem equality_flat_no_witness {M : TypeMap} [ProvableType M]
    (pair : ProvablePair M M (Expression (F circomPrime))) (off : ℕ) :
    ∀ x ∈ (((Gadgets.Equality.circuit (F := F circomPrime) M).main pair).operations off).toFlat,
      match x with | .witness _ _ => False | _ => True := by
  rcases pair with ⟨lhs, rhs⟩
  unfold Gadgets.Equality.circuit
  simp only [Gadgets.Equality.main]
  intro x hx
  rw [Circuit.forEach.operations_eq, toFlat_flatten, List.map_ofFn, List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  simp only [Function.comp, Circuit.assertZero, circuit_norm, Operations.toFlat,
    List.mem_cons, List.not_mem_nil, or_false] at hxl
  subst hxl
  trivial

/-- `x === y` (an `Equality` assertion) is structurally computable at any offsets. -/
theorem assertEq_structural_any {P : TypeMap} [CircuitType P] {M : TypeMap} [ProvableType M]
    (pin : Var P (F circomPrime)) (pair : ProvablePair M M (Expression (F circomPrime)))
    (subOffset structuralOffset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
      FSCW pin env env' structuralOffset
        (((Gadgets.Equality.circuit (F := F circomPrime) M).main pair).operations subOffset).toFlat :=
  flatStructural_of_no_witness pin env env' _ _ (equality_flat_no_witness pair subOffset)

/-- Same, for the `toSubcircuit` spelling. -/
theorem equality_subcircuit_flatStructural_any
    {P : TypeMap} [CircuitType P] {M : TypeMap} [ProvableType M]
    (pin : Var P (F circomPrime)) (pair : ProvablePair M M (Expression (F circomPrime)))
    (subOffset structuralOffset : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
      FSCW pin env env' structuralOffset
        ((Gadgets.Equality.circuit (F := F circomPrime) M).toSubcircuit subOffset pair).ops.toFlat := by
  rw [FormalAssertion.toSubcircuit]
  simp only [Operations.toNested_toFlat]
  exact assertEq_structural_any pin pair subOffset structuralOffset env env'

/-- The nested-operations form of the same fact. -/
theorem equality_structural_any {P : TypeMap} [CircuitType P] {M : TypeMap} [ProvableType M]
    (pin : Var P (F circomPrime)) (pair : ProvablePair M M (Expression (F circomPrime))) (n : ℕ)
    (env env' : ProverEnvironment (F circomPrime)) :
    SCW pin env env' n
      ((assertion (Gadgets.Equality.circuit (F := F circomPrime) M) pair).operations n) :=
  (Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff
      (Gadgets.Equality.circuit (F := F circomPrime) M) pin pair n env env').mpr
    (assertEq_structural_any pin pair n n env env')

end CW

/-! ## The loop formers stay opaque

A structural peel matches on the circuit former, never on the operation list the
former produces.  Keeping the loop combinators irreducible stops the unifier from
evaluating a 1024-iteration `forEach` while it matches a peel lemma (which is a
`whnf` timeout, or a recursion-depth overflow, rather than a slow proof). -/
attribute [local irreducible] Circuit.forEach Circuit.map Circuit.mapFinRange Circuit.foldlRange
attribute [local irreducible] SubAutomaton.mass MainAutomaton.plainMass MainAutomaton.gatedMass

/-! ## Witnessed product -/

namespace Mul

open CW

/-- Both factors of a `Mul` are read off the gadget's own input. -/
theorem stable_a (inp : Var Inputs (F circomPrime)) (n : ℕ) : Stable n inp inp.a := by
  intro env env' _ hi
  simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.a) hi

theorem stable_b (inp : Var Inputs (F circomPrime)) (n : ℕ) : Stable n inp inp.b := by
  intro env env' _ hi
  simpa [circuit_norm] using congrArg (fun x : Inputs (F circomPrime) => x.b) hi

theorem computableWitnesses : (Mul.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' Mul.main rfl fun offset input env env' => ?_
  unfold Mul.main
  simp only [circuit_norm]
  intro _ hi
  rw [hi]

@[circuit_norm]
theorem localLength_eq (inp : Var Inputs (F circomPrime)) :
    Mul.circuit.localLength inp = 1 := rfl

@[circuit_norm]
theorem output_eq (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    Mul.circuit.output inp n = (var ⟨n⟩ : Expression (F circomPrime)) := rfl

@[circuit_norm]
theorem sub_localLength_eq (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    (subcircuit Mul.circuit inp).localLength n = 1 := rfl

@[circuit_norm]
theorem sub_output_eq (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    (subcircuit Mul.circuit inp).output n = (var ⟨n⟩ : Expression (F circomPrime)) := rfl

/-- A witnessed product sits structurally wherever its two factors are stable. -/
theorem flat_mul {P : TypeMap} [CircuitType P] (pin : Var P (F circomPrime))
    (a b : Expression (F circomPrime)) (n m : ℕ) (hnm : m = n)
    (ha : CW.Stable m pin a) (hb : CW.Stable m pin b)
    (env env' : ProverEnvironment (F circomPrime)) :
    CW.FSCW pin env env' n (Mul.circuit.toSubcircuit m { a := a, b := b }).ops.toFlat := by
  refine CW.flat_subcircuit Mul.circuit pin _ n m hnm ?_ Mul.computableWitnesses env env'
  intro e e' hagree hp
  simp only [circuit_norm]
  exact ⟨ha e e' hagree hp, hb e e' hagree hp⟩

end Mul

namespace Emit

open CW

theorem computableWitnesses : (Emit.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' Emit.main rfl fun offset input env env' => ?_
  unfold Emit.main Rows.mul
  have hinStr : ∀ n, Stable n input input.inStr := fun n =>
    Stable.of_eval (fun v => v.inStr) fun env => by simp [circuit_norm]
  have hsub : ∀ (n j : ℕ) (hj : j < Model.nSub), Stable n input (input.subPrev[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.subPrev[j]'hj) fun env => ?_
    simp [circuit_norm]
  have hune : ∀ n, Stable n input input.isUnescaped := fun n =>
    Stable.of_eval (fun v => v.isUnescaped) fun env => by simp [circuit_norm]
  have hesc : ∀ n, Stable n input input.isSimpleEsc := fun n =>
    Stable.of_eval (fun v => v.isSimpleEsc) fun env => by simp [circuit_norm]
  have hhex : ∀ n, Stable n input input.isHex := fun n =>
    Stable.of_eval (fun v => v.isHex) fun env => by simp [circuit_norm]
  have hcont : ∀ n, Stable n input input.isCont := fun n =>
    Stable.of_eval (fun v => v.isCont) fun env => by simp [circuit_norm]
  simp only [CW.bind_iff, CW.subcircuit_iff, CW.pure_iff, Mul.sub_localLength_eq,
    Mul.sub_output_eq, and_true]
  and_intros
  all_goals refine Mul.flat_mul input _ _ _ _ rfl ?_ ?_ env env'
  all_goals stable_tac

theorem sub_output_main (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    (subcircuit Emit.circuit inp).output n = (Emit.main inp).output n :=
  CW.sub_output_main Emit.circuit inp n

end Emit


/-! ## The `circomlib` comparators

`ByteClass` calls `IsEqual` and `Num2Bits`, `AsciiCheck` calls `LessThan`; each
witnesses only values that are functions of its own input and of already
allocated cells. -/

namespace IsZeroCW

open CW

theorem computableWitnesses :
    (IsZero.circuit (p := circomPrime)).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' IsZero.main rfl fun offset input env env' => ?_
  unfold IsZero.main
  simp only [CW.witness_field_eq, HasAssignEq.assignEq,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    have hx : Expression.eval env.toEnvironment input
        = Expression.eval env'.toEnvironment input := by
      simpa [circuit_norm] using h_input
    show Witgen.FExpr.eval { env := env } _ = Witgen.FExpr.eval { env := env' } _
    exact congrArg (fun x : F circomPrime =>
      Witgen.FExpr.eval { env := env } (.ite (.feq (.const x) (.const 0)) (.const 0)
        (.inv (.const x)))) hx
  · intro h_agree h_input
    have hx : Expression.eval env.toEnvironment input
        = Expression.eval env'.toEnvironment input := by
      simpa [circuit_norm] using h_input
    have hinv : env.get offset = env'.get offset := by
      apply h_agree
      simp [circuit_norm]
    simp only [Expression.eval, Circuit.witnessField, Circuit.witnessVar, Circuit.output,
      circuit_norm]
    rw [hx, hinv]
  all_goals
    first
      | exact CW.equality_subcircuit_flatStructural_any (M := field) input _ _ _ env env'
      | trivial

end IsZeroCW

namespace IsEqualCW

open CW

theorem eval_pair_fst {a : Var fieldPair (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)} (h : eval env a = eval env' a) :
    Expression.eval env.toEnvironment a.1 = Expression.eval env'.toEnvironment a.1 := by
  simpa [circuit_norm] using congrArg Prod.fst h

theorem eval_pair_snd {a : Var fieldPair (F circomPrime)}
    {env env' : ProverEnvironment (F circomPrime)} (h : eval env a = eval env' a) :
    Expression.eval env.toEnvironment a.2 = Expression.eval env'.toEnvironment a.2 := by
  simpa [circuit_norm] using congrArg Prod.snd h

theorem computableWitnesses :
    (IsEqual.circuit (p := circomPrime)).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' IsEqual.main rfl fun offset input env env' => ?_
  unfold IsEqual.main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
    and_true]
  refine Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    IsZero.circuit input _ offset ?_ IsZeroCW.computableWitnesses env env'
  intro e e' h
  simp only [circuit_norm, Expression.eval]
  rw [eval_pair_fst h, eval_pair_snd h]

@[circuit_norm]
theorem localLength_eq (inp : Var fieldPair (F circomPrime)) :
    (IsEqual.circuit (p := circomPrime)).localLength inp = 2 := rfl

@[circuit_norm]
theorem output_eq (inp : Var fieldPair (F circomPrime)) (n : ℕ) :
    (IsEqual.circuit (p := circomPrime)).output inp n
      = (var ⟨n + 1⟩ : Expression (F circomPrime)) := rfl

@[circuit_norm]
theorem sub_localLength_eq (inp : Var fieldPair (F circomPrime)) (n : ℕ) :
    (subcircuit (IsEqual.circuit (p := circomPrime)) inp).localLength n = 2 := rfl

@[circuit_norm]
theorem sub_output_eq (inp : Var fieldPair (F circomPrime)) (n : ℕ) :
    (subcircuit (IsEqual.circuit (p := circomPrime)) inp).output n
      = (var ⟨n + 1⟩ : Expression (F circomPrime)) := rfl

theorem flat_isEqual {P : TypeMap} [CircuitType P] (pin : Var P (F circomPrime))
    (a b : Expression (F circomPrime)) (n m : ℕ) (hnm : m = n)
    (ha : CW.Stable m pin a) (hb : CW.Stable m pin b)
    (env env' : ProverEnvironment (F circomPrime)) :
    CW.FSCW pin env env' n
      ((IsEqual.circuit (p := circomPrime)).toSubcircuit m (a, b)).ops.toFlat := by
  refine CW.flat_subcircuit IsEqual.circuit pin _ n m hnm ?_ computableWitnesses env env'
  intro e e' hagree hp
  simp only [circuit_norm, Prod.mk.injEq]
  exact ⟨ha e e' hagree hp, hb e e' hagree hp⟩

end IsEqualCW

namespace Num2BitsCW

open CW

/-- `Num2Bits`' inner circuit: one witness row (the bits of the input) plus
booleanity and recomposition assertions. -/
theorem arbitrary_computableWitnesses (n : ℕ) :
    (Num2Bits.arbitraryBitLengthCircuit (p := circomPrime) n).base.ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' (Num2Bits.main n) rfl fun offset input env env' => ?_
  unfold Num2Bits.main
  simp only [
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.foldlRange_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    have hx : Expression.eval env.toEnvironment input
        = Expression.eval env'.toEnvironment input := by
      simpa [circuit_norm] using h_input
    ext i hi
    simp [circuit_norm, hx]
  all_goals
    first
      | intro i
      | skip
  all_goals
    first
      | exact CW.equality_subcircuit_flatStructural_any (M := field) input _ _ _ env env'
      | exact CW.equality_structural_any (M := field) input _ _ env env'
      | trivial

theorem computableWitnesses (n : ℕ) (hn : 2 ^ n < circomPrime) :
    (Num2Bits.circuit (p := circomPrime) n hn).base.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition
      input env env')
    (((Num2Bits.arbitraryBitLengthCircuit (p := circomPrime) n) input).operations offset)
  apply CW.forAllFlat_of
  exact ⟨Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses
    (Num2Bits.arbitraryBitLengthCircuit n) input input offset (fun _ _ h => h)
    (arbitrary_computableWitnesses n) env env', trivial⟩

@[circuit_norm]
theorem sub_localLength_eq (k : ℕ) (hk : 2 ^ k < circomPrime)
    (x : Var field (F circomPrime)) (n : ℕ) :
    (subcircuitWithAssertion (Num2Bits.circuit (p := circomPrime) k hk) x).localLength n = k := rfl

@[circuit_norm]
theorem sub_output_eq (k : ℕ) (hk : 2 ^ k < circomPrime)
    (x : Var field (F circomPrime)) (n : ℕ) :
    (subcircuitWithAssertion (Num2Bits.circuit (p := circomPrime) k hk) x).output n
      = varFromOffset (fields k) n := rfl

@[circuit_norm]
theorem localLength_eq (k : ℕ) (hk : 2 ^ k < circomPrime) (x : Var field (F circomPrime)) :
    (Num2Bits.circuit (p := circomPrime) k hk).localLength x = k := rfl

theorem flat_num2Bits (k : ℕ) (hk : 2 ^ k < circomPrime)
    {P : TypeMap} [CircuitType P] (pin : Var P (F circomPrime))
    (x : Expression (F circomPrime)) (n m : ℕ) (hnm : m = n)
    (hx : CW.Stable m pin x)
    (env env' : ProverEnvironment (F circomPrime)) :
    CW.FSCW pin env env' n
      ((Num2Bits.circuit (p := circomPrime) k hk).toSubcircuit m x).ops.toFlat := by
  refine CW.flat_general (Num2Bits.circuit k hk) pin _ n m hnm ?_
    (computableWitnesses k hk) env env'
  intro e e' hagree hp
  simp only [circuit_norm]
  exact hx e e' hagree hp

end Num2BitsCW

namespace LessThanCW

open CW

theorem computableWitnesses (n : ℕ) (hn : 2 ^ (n + 1) < circomPrime) :
    (LessThan.circuit (p := circomPrime) n hn).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' (LessThan.main n hn) rfl fun offset input env env' => ?_
  unfold LessThan.main
  simp only [HasAssignEq.assignEq,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
    Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · refine Challenge.Utils.ComputableWitnessLemmas.GeneralFormalCircuit.subcircuit_flatStructuralComputableWitnesses
      (Num2Bits.circuit (n + 1) hn) input _ offset ?_ (Num2BitsCW.computableWitnesses _ hn) env env'
    intro e e' h
    simp only [circuit_norm, Expression.eval]
    rw [IsEqualCW.eval_pair_fst h, IsEqualCW.eval_pair_snd h]
  · trivial
  · intro h_agree _
    simp only [circuit_norm, Num2Bits.circuit,
      Num2Bits.arbitraryBitLengthCircuit] at h_agree ⊢
    rw [h_agree (offset + n) (by omega)]
  all_goals
    first
      | exact CW.equality_subcircuit_flatStructural_any (M := field) input _ _ _ env env'
      | exact CW.equality_structural_any (M := field) input _ _ env env'
      | trivial

theorem flat_lessThan (k : ℕ) (hk : 2 ^ (k + 1) < circomPrime)
    {P : TypeMap} [CircuitType P] (pin : Var P (F circomPrime))
    (a b : Expression (F circomPrime)) (n m : ℕ) (hnm : m = n)
    (ha : CW.Stable m pin a) (hb : CW.Stable m pin b)
    (env env' : ProverEnvironment (F circomPrime)) :
    CW.FSCW pin env env' n
      ((LessThan.circuit (p := circomPrime) k hk).toSubcircuit m (a, b)).ops.toFlat := by
  refine CW.flat_subcircuit (LessThan.circuit k hk) pin _ n m hnm ?_
    (computableWitnesses k hk) env env'
  intro e e' hagree hp
  simp only [circuit_norm, Prod.mk.injEq]
  exact ⟨ha e e' hagree hp, hb e e' hagree hp⟩

end LessThanCW

namespace ValueEmit

open CW

theorem computableWitnesses : (ValueEmit.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' ValueEmit.main rfl fun offset input env env' => ?_
  have hemit : ∀ n, Stable n input input.emit := fun n =>
    Stable.of_eval (fun v => v.emit) fun env => by simp [circuit_norm]
  have hstStr : ∀ n, Stable n input input.stStr := fun n =>
    Stable.of_eval (fun v => v.stStr) fun env => by simp [circuit_norm]
  have hisDigit : ∀ n, Stable n input input.isDigit := fun n =>
    Stable.of_eval (fun v => v.isDigit) fun env => by simp [circuit_norm]
  have hstNum : ∀ n, Stable n input input.stNum := fun n =>
    Stable.of_eval (fun v => v.stNum) fun env => by simp [circuit_norm]
  have hkStrInt : ∀ n, Stable n input input.kStrInt := fun n =>
    Stable.of_eval (fun v => v.kStrInt) fun env => by simp [circuit_norm]
  have hcp : ∀ n, Stable n input input.cp := fun n =>
    Stable.of_eval (fun v => v.cp) fun env => by simp [circuit_norm]
  have hbyte : ∀ n, Stable n input input.byte := fun n =>
    Stable.of_eval (fun v => v.byte) fun env => by simp [circuit_norm]
  unfold ValueEmit.main Rows.mul
  simp only [CW.bind_iff, CW.subcircuit_iff, CW.pure_iff, Mul.sub_localLength_eq,
    Mul.sub_output_eq, and_true]
  and_intros
  all_goals
    refine CW.flat_subcircuit Mul.circuit input _ _ _ rfl ?_ Mul.computableWitnesses env env'
  all_goals stableP_tac

theorem sub_output_main (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    (subcircuit ValueEmit.circuit inp).output n = (ValueEmit.main inp).output n :=
  CW.sub_output_main ValueEmit.circuit inp n

end ValueEmit

namespace CodePoint

open CW

theorem computableWitnesses : (CodePoint.circuit).base.ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' CodePoint.main rfl fun offset input env env' => ?_
  have hbyte : ∀ n, Stable n input input.byte := fun n =>
    Stable.of_eval (fun v => v.byte) fun env => by simp [circuit_norm]
  have hisDigit : ∀ n, Stable n input input.isDigit := fun n =>
    Stable.of_eval (fun v => v.isDigit) fun env => by simp [circuit_norm]
  have hisUpperHex : ∀ n, Stable n input input.isUpperHex := fun n =>
    Stable.of_eval (fun v => v.isUpperHex) fun env => by simp [circuit_norm]
  have hisLowerHex : ∀ n, Stable n input input.isLowerHex := fun n =>
    Stable.of_eval (fun v => v.isLowerHex) fun env => by simp [circuit_norm]
  have hescVal : ∀ n, Stable n input input.escVal := fun n =>
    Stable.of_eval (fun v => v.escVal) fun env => by simp [circuit_norm]
  have hemitPlain : ∀ n, Stable n input input.emitPlain := fun n =>
    Stable.of_eval (fun v => v.emitPlain) fun env => by simp [circuit_norm]
  have hemitEsc : ∀ n, Stable n input input.emitEsc := fun n =>
    Stable.of_eval (fun v => v.emitEsc) fun env => by simp [circuit_norm]
  have hemitU : ∀ n, Stable n input input.emitU := fun n =>
    Stable.of_eval (fun v => v.emitU) fun env => by simp [circuit_norm]
  have hemitUtf8 : ∀ n, Stable n input input.emitUtf8 := fun n =>
    Stable.of_eval (fun v => v.emitUtf8) fun env => by simp [circuit_norm]
  have hinH : ∀ n, Stable n input input.inH := fun n =>
    Stable.of_eval (fun v => v.inH) fun env => by simp [circuit_norm]
  have hhexAccPrev : ∀ n, Stable n input input.hexAccPrev := fun n =>
    Stable.of_eval (fun v => v.hexAccPrev) fun env => by simp [circuit_norm]
  have hhexAccNext : ∀ n, Stable n input input.hexAccNext := fun n =>
    Stable.of_eval (fun v => v.hexAccNext) fun env => by simp [circuit_norm]
  have hactive : ∀ n, Stable n input input.active := fun n =>
    Stable.of_eval (fun v => v.active) fun env => by simp [circuit_norm]
  unfold CodePoint.main Rows.freeze Rows.mul
  simp only [CW.bind_iff, CW.subcircuit_iff, CW.assertZero_iff, CW.pure_iff,
    Mul.sub_localLength_eq, Mul.sub_output_eq, and_true]
  and_intros
  all_goals
    refine CW.flat_subcircuit Mul.circuit input _ _ _ rfl ?_ Mul.computableWitnesses env env'
  all_goals stableP_tac

theorem sub_output_main (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    (subcircuitWithAssertion CodePoint.circuit inp).output n = (CodePoint.main inp).output n :=
  CW.subWithAssertion_output_main CodePoint.circuit inp n

end CodePoint

namespace AsciiCheck

open CW

theorem computableWitnesses : (AsciiCheck.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' AsciiCheck.main rfl fun offset input env env' => ?_
  have hcp : ∀ n, Stable n input input.cp := fun n =>
    Stable.of_eval (fun v => v.cp) fun env => by simp [circuit_norm]
  have hwrite : ∀ n, Stable n input input.write := fun n =>
    Stable.of_eval (fun v => v.write) fun env => by simp [circuit_norm]
  have hstStr : ∀ n, Stable n input input.stStr := fun n =>
    Stable.of_eval (fun v => v.stStr) fun env => by simp [circuit_norm]
  unfold AsciiCheck.main Rows.mul
  simp only [CW.bind_iff, CW.subcircuit_iff, CW.assertZero_iff, CW.pure_iff, and_true]
  and_intros
  · refine CW.flat_subcircuit (LessThan.circuit 16 two_pow_17_lt) input _ _ _ rfl ?_
      (LessThanCW.computableWitnesses 16 two_pow_17_lt) env env'
    stableP_tac
  · refine CW.flat_subcircuit Mul.circuit input _ _ _ rfl ?_ Mul.computableWitnesses env env'
    stableP_tac

end AsciiCheck


/-! ## One-hot of a small value -/

namespace OneHot

open CW

theorem computableWitnesses (n : ℕ) [NeZero n] : (OneHot.circuit n).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' (OneHot.main n) rfl fun offset input env env' => ?_
  unfold OneHot.main
  simp only [CW.bind_iff, CW.witnessVector_iff, CW.forEach_iff, CW.assertZero_iff,
    CW.pure_iff, and_true, true_and, implies_true]
  intro _ h_input
  have hx : Expression.eval env.toEnvironment input.x
      = Expression.eval env'.toEnvironment input.x := by
    simpa [circuit_norm] using congrArg (fun z : OneHot.Inputs (F circomPrime) => z.x) h_input
  exact congrArg (fun c : F circomPrime => Witgen.VExpr.eval { env := env }
    (Witgen.VExpr.range n fun i => (i =? Witgen.U64Expr.val (Witgen.FExpr.const c)).toField)) hx

@[circuit_norm]
theorem localLength_eq (n : ℕ) [NeZero n] (inp : Var Inputs (F circomPrime)) :
    (OneHot.circuit n).localLength inp = n := rfl

@[circuit_norm]
theorem output_eq (n : ℕ) [NeZero n] (inp : Var Inputs (F circomPrime)) (k : ℕ) :
    (OneHot.circuit n).output inp k = varFromOffset (fields n) k := rfl

@[circuit_norm]
theorem sub_localLength_eq (n : ℕ) [NeZero n] (inp : Var Inputs (F circomPrime)) (k : ℕ) :
    (subcircuit (OneHot.circuit n) inp).localLength k = n := rfl

@[circuit_norm]
theorem sub_output_eq (n : ℕ) [NeZero n] (inp : Var Inputs (F circomPrime)) (k : ℕ) :
    (subcircuit (OneHot.circuit n) inp).output k = varFromOffset (fields n) k := rfl

end OneHot

/-! ## The structural peel

`simp only [circuit_norm]` cannot be used for the peel: it unfolds
`Circuit.operations` and `Circuit.localLength`, which destroys the key of every
peeling lemma (and of the loop-length lemmas).  `cw_peel` is the explicit set
instead: one entry per circuit former, plus the `rfl` lengths and outputs of the
gadgets used as children.  Extra lemmas for a caller's own children are passed in
brackets. -/

@[circuit_norm]
theorem assertZero_localLength (e : Expression (F circomPrime)) (n : ℕ) :
    (Circuit.assertZero e).localLength n = 0 := rfl

syntax "cw_peel" : tactic
syntax "cw_peel" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| cw_peel) => `(tactic| cw_peel [and_true])
  | `(tactic| cw_peel [$ts,*]) => `(tactic|
      simp only [$ts,*, CW.bind_iff, CW.pure_iff, CW.subcircuit_iff,
        CW.subcircuitWithAssertion_iff, CW.assertion_iff, CW.assertZero_iff,
        CW.witnessVector_iff, CW.witnessIR_iff, CW.witnessVar_iff, CW.witnessField_iff,
        CW.forEach_iff, CW.mapFinRange_iff, CW.foldlRange_iff, CW.map_iff,
        Vector.getElem_mapIdx,
        Circuit.bind_localLength_eq, Circuit.pure_localLength_eq,
        Circuit.forEach.localLength_eq, Circuit.map.localLength_eq,
        Circuit.mapFinRange.localLength_eq, Solution.JSONExtract.assertZero_localLength,
        Circuit.bind_output_eq, Circuit.pure_output_eq, Circuit.map.output_eq,
        Circuit.mapFinRange.output_eq,
        Mul.sub_localLength_eq, Mul.sub_output_eq, Mul.localLength_eq, Mul.output_eq,
        OneHot.sub_localLength_eq, OneHot.sub_output_eq, OneHot.localLength_eq,
        OneHot.output_eq, IsEqualCW.sub_localLength_eq, IsEqualCW.sub_output_eq,
        IsEqualCW.localLength_eq, IsEqualCW.output_eq, Num2BitsCW.sub_localLength_eq,
        Num2BitsCW.localLength_eq, Num2BitsCW.sub_output_eq,
        ProvableType.varFromOffset_fields, Vector.getElem_mapRange, Vector.getElem_finRange,
        Model.nClaims, Model.kIdxMax, Model.ofsMax, Model.nSt, Model.nSub,
        and_true, true_and, implies_true, Nat.add_zero, Nat.zero_add, Nat.mul_one,
        Nat.one_mul])

syntax "cw_peel!" : tactic
syntax "cw_peel!" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| cw_peel!) => `(tactic| cw_peel! [and_true])
  | `(tactic| cw_peel! [$ts,*]) => `(tactic|
      simp (config := { maxSteps := 2000000 }) only [$ts,*, CW.bind_iff, CW.pure_iff, CW.subcircuit_iff,
        CW.subcircuitWithAssertion_iff, CW.assertion_iff, CW.assertZero_iff,
        CW.witnessVector_iff, CW.witnessIR_iff, CW.witnessVar_iff, CW.witnessField_iff,
        CW.forEach_iff, CW.mapFinRange_iff, CW.foldlRange_iff, CW.map_iff,
        Vector.getElem_mapIdx,
        Circuit.bind_localLength_eq, Circuit.pure_localLength_eq,
        Circuit.forEach.localLength_eq, Circuit.map.localLength_eq,
        Circuit.mapFinRange.localLength_eq, Solution.JSONExtract.assertZero_localLength,
        Circuit.bind_output_eq, Circuit.pure_output_eq, Circuit.map.output_eq,
        Circuit.mapFinRange.output_eq,
        Mul.sub_localLength_eq, Mul.sub_output_eq, Mul.localLength_eq, Mul.output_eq,
        OneHot.sub_localLength_eq, OneHot.sub_output_eq, OneHot.localLength_eq,
        OneHot.output_eq, IsEqualCW.sub_localLength_eq, IsEqualCW.sub_output_eq,
        IsEqualCW.localLength_eq, IsEqualCW.output_eq, Num2BitsCW.sub_localLength_eq,
        Num2BitsCW.localLength_eq, Num2BitsCW.sub_output_eq,
        ProvableType.varFromOffset_fields, Vector.getElem_mapRange, Vector.getElem_finRange,
        Model.nClaims, Model.kIdxMax, Model.ofsMax, Model.nSt, Model.nSub,
        and_true, true_and, implies_true, Nat.add_zero, Nat.zero_add, Nat.mul_one,
        Nat.one_mul])

/-! ## Filled-prefix mask -/

namespace FilledMask

open CW

theorem computableWitnesses (n : ℕ) [NeZero n] : (FilledMask.circuit n).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' (FilledMask.main n) rfl fun offset input env env' => ?_
  unfold FilledMask.main
  simp only [CW.bind_iff, CW.witnessVector_iff, CW.forEach_iff, CW.assertZero_iff,
    CW.pure_iff, and_true, true_and, implies_true]
  intro _ h_input
  have hx : Expression.eval env.toEnvironment input.len
      = Expression.eval env'.toEnvironment input.len := by
    simpa [circuit_norm] using congrArg (fun z : FilledMask.Inputs n (F circomPrime) => z.len) h_input
  exact congrArg (fun c : F circomPrime => Witgen.VExpr.eval { env := env }
    (Witgen.VExpr.range n fun t => (t <? Witgen.U64Expr.val (Witgen.FExpr.const c)).toField)) hx

@[circuit_norm]
theorem main_eq (n : ℕ) [NeZero n] :
    (FilledMask.circuit n).main = FilledMask.main n := rfl

/-- The filled-prefix mask witnesses only from the claimed length, so a caller
needs no agreement on the cells. -/
theorem flat_sub {P : TypeMap} [CircuitType P] (pin : Var P (F circomPrime)) {n : ℕ} [NeZero n]
    (cells : Vector (Expression (F circomPrime)) n) (len : Expression (F circomPrime))
    (k m : ℕ) (hkm : m = k) (hlen : CW.Stable m pin len)
    (env env' : ProverEnvironment (F circomPrime)) :
    CW.FSCW pin env env' k
      ((((FilledMask.circuit n).main { cells := cells, len := len }).operations m).toFlat) := by
  refine CW.flat_assertion_of_structural (FilledMask.circuit n) pin _ k m hkm env env' ?_
  rw [main_eq]
  unfold FilledMask.main
  cw_peel
  intro ha hp
  exact congrArg (fun c : F circomPrime => Witgen.VExpr.eval { env := env }
    (Witgen.VExpr.range n fun t => (t <? Witgen.U64Expr.val (Witgen.FExpr.const c)).toField))
    (hlen env env' ha hp)

end FilledMask



namespace Matcher

open CW

theorem computableWitnesses (k : Model.Claim) :
    (Matcher.circuit k).base.ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' (Matcher.main k) rfl
    fun offset input env env' => ?_
  have hcp : ∀ n, Stable n input input.cp := fun n =>
    Stable.of_eval (fun v => v.cp) fun env => by simp [circuit_norm]
  have hemit : ∀ n, Stable n input input.emit := fun n =>
    Stable.of_eval (fun v => v.emit) fun env => by simp [circuit_norm]
  have hmPrev : ∀ n, Stable n input input.mPrev := fun n =>
    Stable.of_eval (fun v => v.mPrev) fun env => by simp [circuit_norm]
  have hmNext : ∀ n, Stable n input input.mNext := fun n =>
    Stable.of_eval (fun v => v.mNext) fun env => by simp [circuit_norm]
  have hkeyStart : ∀ n, Stable n input input.keyStart := fun n =>
    Stable.of_eval (fun v => v.keyStart) fun env => by simp [circuit_norm]
  have hkeyClose : ∀ n, Stable n input input.keyClose := fun n =>
    Stable.of_eval (fun v => v.keyClose) fun env => by simp [circuit_norm]
  have hstKey : ∀ n, Stable n input input.stKey := fun n =>
    Stable.of_eval (fun v => v.stKey) fun env => by simp [circuit_norm]
  have hactive : ∀ n, Stable n input input.active := fun n =>
    Stable.of_eval (fun v => v.active) fun env => by simp [circuit_norm]
  have hkIdxOH : ∀ (n j : ℕ) (hj : j < Model.kIdxMax), Stable n input (input.kIdxOH[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.kIdxOH[j]'hj) fun env => ?_
    simp [circuit_norm]
  have hexpected : ∀ n, Stable n input (Fin.foldl Model.kIdxMax (fun acc t =>
      acc + input.kIdxOH[t] *
        (((Model.nameAt k t.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0) := by
    intro n
    refine Stable.finFoldl _ _ _ (Stable.const 0) fun acc t hacc => ?_
    exact hacc.add ((hkIdxOH n t.val t.isLt).mul (Stable.const _))
  unfold Matcher.main
  cw_peel
  and_intros
  all_goals first
    | (refine IsEqualCW.flat_isEqual input _ _ _ _ (by first | rfl | omega) ?_ ?_ env env'
       · exact hcp _
       · exact hexpected _)
    | (refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_ Mul.computableWitnesses env env'
       stableP_tac)

end Matcher

namespace KeyIndex

open CW

theorem computableWitnesses : (KeyIndex.circuit).base.ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' KeyIndex.main rfl fun offset input env env' => ?_
  have hstKeyPrev : ∀ n, Stable n input input.stKeyPrev := fun n =>
    Stable.of_eval (fun v => v.stKeyPrev) fun env => by simp [circuit_norm]
  have hstKeyNext : ∀ n, Stable n input input.stKeyNext := fun n =>
    Stable.of_eval (fun v => v.stKeyNext) fun env => by simp [circuit_norm]
  have hcloseQuote : ∀ n, Stable n input input.closeQuote := fun n =>
    Stable.of_eval (fun v => v.closeQuote) fun env => by simp [circuit_norm]
  have hemit : ∀ n, Stable n input input.emit := fun n =>
    Stable.of_eval (fun v => v.emit) fun env => by simp [circuit_norm]
  have hkIdxPrev : ∀ n, Stable n input input.kIdxPrev := fun n =>
    Stable.of_eval (fun v => v.kIdxPrev) fun env => by simp [circuit_norm]
  have hkIdxNext : ∀ n, Stable n input input.kIdxNext := fun n =>
    Stable.of_eval (fun v => v.kIdxNext) fun env => by simp [circuit_norm]
  have hactive : ∀ n, Stable n input input.active := fun n =>
    Stable.of_eval (fun v => v.active) fun env => by simp [circuit_norm]
  unfold KeyIndex.main Rows.freeze Rows.mul
  cw_peel
  refine ⟨?_, ?_, ?oh, ?_, ?_, ?_⟩
  case oh =>
    refine CW.flat_subcircuit (OneHot.circuit Model.kIdxMax) input _ _ _ (by first | rfl | omega) ?_
      (OneHot.computableWitnesses _) env env'
    stableP_tac
  all_goals
    refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
      Mul.computableWitnesses env env'
  all_goals stableP_tac

theorem sub_output_main (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    (subcircuitWithAssertion KeyIndex.circuit inp).output n = (KeyIndex.main inp).output n :=
  CW.subWithAssertion_output_main KeyIndex.circuit inp n

end KeyIndex

namespace Offset

open CW

theorem computableWitnesses : (Offset.circuit).base.ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' Offset.main rfl fun offset input env env' => ?_
  have hofsPrev : ∀ n, Stable n input input.ofsPrev := fun n =>
    Stable.of_eval (fun v => v.ofsPrev) fun env => by simp [circuit_norm]
  have hofsNext : ∀ n, Stable n input input.ofsNext := fun n =>
    Stable.of_eval (fun v => v.ofsNext) fun env => by simp [circuit_norm]
  have hvEmit : ∀ n, Stable n input input.vEmit := fun n =>
    Stable.of_eval (fun v => v.vEmit) fun env => by simp [circuit_norm]
  have hinVal : ∀ n, Stable n input input.inVal := fun n =>
    Stable.of_eval (fun v => v.inVal) fun env => by simp [circuit_norm]
  have hactive : ∀ n, Stable n input input.active := fun n =>
    Stable.of_eval (fun v => v.active) fun env => by simp [circuit_norm]
  unfold Offset.main Rows.freeze Rows.mul
  cw_peel
  refine ⟨?oh, ?_, ?_, ?_⟩
  case oh =>
    refine CW.flat_subcircuit (OneHot.circuit Model.ofsMax) input _ _ _ (by first | rfl | omega) ?_
      (OneHot.computableWitnesses _) env env'
    stableP_tac
  all_goals
    refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
      Mul.computableWitnesses env env'
  all_goals stableP_tac

theorem sub_output_main (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    (subcircuitWithAssertion Offset.circuit inp).output n = (Offset.main inp).output n :=
  CW.subWithAssertion_output_main Offset.circuit inp n

end Offset

namespace ClaimSignals

open CW

theorem computableWitnesses : (ClaimSignals.circuit).base.ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' ClaimSignals.main rfl
    fun offset input env env' => ?_
  have hvEmit : ∀ n, Stable n input input.vEmit := fun n =>
    Stable.of_eval (fun v => v.vEmit) fun env => by simp [circuit_norm]
  have hstPval : ∀ n, Stable n input input.stPval := fun n =>
    Stable.of_eval (fun v => v.stPval) fun env => by simp [circuit_norm]
  have hisMinus : ∀ n, Stable n input input.isMinus := fun n =>
    Stable.of_eval (fun v => v.isMinus) fun env => by simp [circuit_norm]
  have hstT3 : ∀ n, Stable n input input.stT3 := fun n =>
    Stable.of_eval (fun v => v.stT3) fun env => by simp [circuit_norm]
  have hisLowerE : ∀ n, Stable n input input.isLowerE := fun n =>
    Stable.of_eval (fun v => v.isLowerE) fun env => by simp [circuit_norm]
  have hnMemPrev : ∀ n, Stable n input input.nMemPrev := fun n =>
    Stable.of_eval (fun v => v.nMemPrev) fun env => by simp [circuit_norm]
  have hnMemNext : ∀ n, Stable n input input.nMemNext := fun n =>
    Stable.of_eval (fun v => v.nMemNext) fun env => by simp [circuit_norm]
  have hkeyStart : ∀ n, Stable n input input.keyStart := fun n =>
    Stable.of_eval (fun v => v.keyStart) fun env => by simp [circuit_norm]
  have hclaimPrev : ∀ (n j : ℕ) (hj : j < Model.nClaims),
      Stable n input (input.claimPrev[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.claimPrev[j]'hj) fun env => ?_
    simp [circuit_norm]
  unfold ClaimSignals.main Rows.mul
  cw_peel
  and_intros
  all_goals first
    | (intro i
       refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_ Mul.computableWitnesses env env'
       stableP_tac)
    | (refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_ Mul.computableWitnesses env env'
       stableP_tac)

theorem sub_output_main (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    (subcircuitWithAssertion ClaimSignals.circuit inp).output n = (ClaimSignals.main inp).output n :=
  CW.subWithAssertion_output_main ClaimSignals.circuit inp n

end ClaimSignals

namespace ClaimReg

open CW

theorem computableWitnesses : (ClaimReg.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' ClaimReg.main rfl fun offset input env env' => ?_
  have hactive : ∀ n, Stable n input input.active := fun n =>
    Stable.of_eval (fun v => v.active) fun env => by simp [circuit_norm]
  have hkeyClose : ∀ n, Stable n input input.keyClose := fun n =>
    Stable.of_eval (fun v => v.keyClose) fun env => by simp [circuit_norm]
  have hkeyStart : ∀ n, Stable n input input.keyStart := fun n =>
    Stable.of_eval (fun v => v.keyStart) fun env => by simp [circuit_norm]
  have hmatch : ∀ (n j : ℕ) (hj : j < Model.nClaims), Stable n input (input.match_[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.match_[j]'hj) fun env => ?_
    simp [circuit_norm]
  have hclaimPrev : ∀ (n j : ℕ) (hj : j < Model.nClaims),
      Stable n input (input.claimPrev[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.claimPrev[j]'hj) fun env => ?_
    simp [circuit_norm]
  have hclaimNext : ∀ (n j : ℕ) (hj : j < Model.nClaims),
      Stable n input (input.claimNext[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.claimNext[j]'hj) fun env => ?_
    simp [circuit_norm]
  unfold ClaimReg.main Rows.freeze Rows.mul
  cw_peel
  intro i
  and_intros
  all_goals
    refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_ Mul.computableWitnesses env env'
  all_goals stableP_tac

end ClaimReg

namespace KeyMatchers

open CW

theorem computableWitnesses : (KeyMatchers.circuit).base.ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' KeyMatchers.main rfl
    fun offset input env env' => ?_
  have hkIdxOH : ∀ (n j : ℕ) (hj : j < Model.kIdxMax), Stable n input (input.kIdxOH[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.kIdxOH[j]'hj) fun env => ?_
    simp [circuit_norm]
  unfold KeyMatchers.main
  cw_peel
  intro i
  refine CW.flat_general (Matcher.circuit i) input _ _ _ (by first | rfl | omega) ?_
    (Matcher.computableWitnesses i) env env'
  stableP_tac

theorem sub_output_main (inp : Var Inputs (F circomPrime)) (n : ℕ) :
    (subcircuitWithAssertion KeyMatchers.circuit inp).output n = (KeyMatchers.main inp).output n :=
  CW.subWithAssertion_output_main KeyMatchers.circuit inp n

end KeyMatchers

/-! ## The byte classifier -/

namespace ByteClass

open CW

set_option maxHeartbeats 1000000 in
theorem computableWitnesses : (ByteClass.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' ByteClass.main rfl fun offset input env env' => ?_
  have hx : ∀ n, Stable n input input := by
    intro n e e' _ hp
    simpa [circuit_norm] using hp
  unfold ByteClass.main ByteClass.mul
  cw_peel! [Num2BitsCW.sub_localLength_eq, Num2BitsCW.sub_output_eq]
  and_intros
  all_goals first
    | (refine IsEqualCW.flat_isEqual input _ _ _ _ (by first | rfl | omega) ?_ ?_ env env' <;>
       stable_tac)
    | (refine Num2BitsCW.flat_num2Bits 8 ByteClass.two_pow_8_lt input _ _ _
         (by first | rfl | omega) ?_ env env'
       stable_tac)
    | (refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
         Mul.computableWitnesses env env'
       stableP_tac)

theorem sub_output_main (inp : Var field (F circomPrime)) (n : ℕ) :
    (subcircuit ByteClass.circuit inp).output n = (ByteClass.main inp).output n :=
  CW.sub_output_main ByteClass.circuit inp n

end ByteClass

/-! ## The two automata -/

namespace SubAutomaton

open CW

set_option maxHeartbeats 1000000 in
theorem computableWitnesses : (SubAutomaton.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' SubAutomaton.main rfl
    fun offset input env env' => ?_
  have hinStr : ∀ n, Stable n input input.inStr := fun n =>
    Stable.of_eval (fun v => v.inStr) fun env => by simp [circuit_norm]
  have hactive : ∀ n, Stable n input input.active := fun n =>
    Stable.of_eval (fun v => v.active) fun env => by simp [circuit_norm]
  have hsubPrev : ∀ (n j : ℕ) (hj : j < Model.nSub), Stable n input (input.subPrev[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.subPrev[j]'hj) fun env => ?_
    simp [circuit_norm]
  have hsubNext : ∀ (n j : ℕ) (hj : j < Model.nSub), Stable n input (input.subNext[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.subNext[j]'hj) fun env => ?_
    simp [circuit_norm]
  have hproj : ∀ (e : Environment (F circomPrime)),
      (ProvableStruct.eval e input).cls = ProvableStruct.eval e input.cls := by
    intro e
    show Eval.eval e input.cls = ProvableStruct.eval e input.cls
    rw [ProvableStruct.eval_eq_eval]
  have hcls : ∀ (n : ℕ) (c : SCls), Stable n input (clsExpr input.cls c) := by
    intro n c
    refine Stable.of_eval (fun v => clsVal v.cls c) fun envX => ?_
    rw [eval_clsExpr]
    congr 1
    try simp only [CircuitType.eval_expression_prover_to_verifier]
    rw [← Step.eval_cls, ← hproj, ← ProvableStruct.eval_eq_eval]
  have hmass : ∀ (n base j : ℕ), base + 23 ≤ n →
      Stable n input (mass (Vector.mapIdx
        (fun i (_ : Edge) => (var ⟨base + i⟩ : Expression (F circomPrime))) edges) j) := by
    intro n base j hb
    simp only [mass]
    refine Stable.finFoldl _ _ _ (Stable.const 0) fun acc e hacc => ?_
    refine Stable.ite _ ?_ hacc
    refine hacc.add ?_
    first
      | (simp only [Fin.getElem_fin, Vector.getElem_mapIdx]
         exact Stable.var (by omega))
      | exact Stable.var (by omega)
  unfold SubAutomaton.main
  cw_peel
  refine ⟨?_, ?_⟩
  · intro i
    refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
      Mul.computableWitnesses env env'
    stableP_tac
  · clear hcls hproj
    intro j
    and_intros
    all_goals
      refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
        Mul.computableWitnesses env env'
    all_goals stableP_tac

end SubAutomaton

namespace MainAutomaton

open CW

set_option maxHeartbeats 1000000 in
theorem computableWitnesses : (MainAutomaton.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' MainAutomaton.main rfl
    fun offset input env env' => ?_
  have hactive : ∀ n, Stable n input input.active := fun n =>
    Stable.of_eval (fun v => v.active) fun env => by simp [circuit_norm]
  have hcloseQuote : ∀ n, Stable n input input.closeQuote := fun n =>
    Stable.of_eval (fun v => v.closeQuote) fun env => by simp [circuit_norm]
  have hstPrev : ∀ (n j : ℕ) (hj : j < Model.nSt), Stable n input (input.stPrev[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.stPrev[j]'hj) fun env => ?_
    simp [circuit_norm]
  have hstNext : ∀ (n j : ℕ) (hj : j < Model.nSt), Stable n input (input.stNext[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.stNext[j]'hj) fun env => ?_
    simp [circuit_norm]
  have hkinds : ∀ (n j : ℕ) (hj : j < 4), Stable n input (input.kinds[j]'hj) := by
    intro n j hj
    refine Stable.of_eval (fun v => v.kinds[j]'hj) fun env => ?_
    simp [circuit_norm]
  have hproj : ∀ (e : Environment (F circomPrime)),
      (ProvableStruct.eval e input).cls = ProvableStruct.eval e input.cls := by
    intro e
    show Eval.eval e input.cls = ProvableStruct.eval e input.cls
    rw [ProvableStruct.eval_eq_eval]
  have hcls : ∀ (n : ℕ) (c : Cls), Stable n input (clsExpr input.cls input.closeQuote c) := by
    intro n c
    refine Stable.of_eval (fun v => clsVal v.cls v.closeQuote c) fun envX => ?_
    rw [eval_clsExpr]
    congr 1
    · try simp only [CircuitType.eval_expression_prover_to_verifier]
      rw [← Step.eval_cls, ← hproj, ← ProvableStruct.eval_eq_eval]
    · simp [circuit_norm]
  have hgate : ∀ (n : ℕ) (g : Gate), Stable n input (gateExpr input.kinds g) := by
    intro n g
    cases g <;>
      simp only [gateExpr] <;>
      first
        | exact (hkinds n 0 (by omega)).add (hkinds n 3 (by omega))
        | exact (hkinds n 1 (by omega)).add (hkinds n 3 (by omega))
        | exact (hkinds n 2 (by omega)).add (hkinds n 3 (by omega))
        | exact hkinds n 3 (by omega)
  have hplain : ∀ (n base j : ℕ), base + 50 ≤ n →
      Stable n input (plainMass (Vector.mapIdx
        (fun i (_ : Edge) => (var ⟨base + i⟩ : Expression (F circomPrime))) plainEdges) j) := by
    intro n base j hb
    simp only [plainMass]
    refine Stable.finFoldl _ _ _ (Stable.const 0) fun acc e hacc => ?_
    refine Stable.ite _ ?_ hacc
    refine hacc.add ?_
    first
      | (simp only [Fin.getElem_fin, Vector.getElem_mapIdx]
         exact Stable.var (by omega))
      | exact Stable.var (by omega)
  have hgated : ∀ (n base j : ℕ), base + 11 * 2 ≤ n →
      Stable n input (gatedMass (Vector.mapIdx
        (fun i (_ : GatedEdge) => (var ⟨base + i * 2 + 1⟩ : Expression (F circomPrime)))
          gatedEdges) j) := by
    intro n base j hb
    simp only [gatedMass]
    refine Stable.finFoldl _ _ _ (Stable.const 0) fun acc e hacc => ?_
    refine Stable.ite _ ?_ hacc
    refine hacc.add ?_
    first
      | (simp only [Fin.getElem_fin, Vector.getElem_mapIdx]
         exact Stable.var (by omega))
      | exact Stable.var (by omega)
  unfold MainAutomaton.main
  cw_peel
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
      Mul.computableWitnesses env env'
    stableP_tac
  · intro i
    and_intros
    all_goals
      refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
        Mul.computableWitnesses env env'
    all_goals stableP_tac
  · clear hcls hgate hproj
    intro j
    refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
      Mul.computableWitnesses env env'
    stableP_tac

end MainAutomaton

/-! ## Routing a value into the output slots -/

namespace RouteSlot

open CW

set_option maxHeartbeats 1000000 in
theorem computableWitnesses (n : ℕ) [NeZero n] (hn : n ≤ Model.ofsMax) :
    (RouteSlot.circuit n hn).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' (RouteSlot.main n hn) rfl
    fun offset input env env' => ?_
  have hclaimFlag : ∀ m, Stable m input input.claimFlag := fun m =>
    Stable.of_eval (fun v => v.claimFlag) fun envX => by simp [circuit_norm]
  have hofsOH : ∀ (m j : ℕ) (hj : j < Model.ofsMax), Stable m input (input.ofsOH[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.ofsOH[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hcells : ∀ (m j : ℕ) (hj : j < n), Stable m input (input.cells[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.cells[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hprods : ∀ (m base : ℕ), base + n ≤ m →
      Stable m input (Fin.foldl n (fun acc t =>
        acc + (Vector.mapIdx (fun i (_ : Fin n) => (var ⟨base + i⟩ : Expression (F circomPrime)))
          (Vector.finRange n))[t]) 0) := by
    intro m base hb
    refine Stable.finFoldl _ _ _ (Stable.const 0) fun acc t hacc => ?_
    refine hacc.add ?_
    first
      | (simp only [Fin.getElem_fin, Vector.getElem_mapIdx]
         exact Stable.var (by omega))
      | exact Stable.var (by omega)
  have hofsSum : ∀ m, Stable m input
      (Fin.foldl n (fun acc t => acc + ofsAt hn input.ofsOH t) 0) := by
    intro m
    refine Stable.finFoldl _ _ _ (Stable.const 0) fun acc t hacc => ?_
    refine hacc.add ?_
    simp only [ofsAt]
    exact hofsOH _ _ _
  unfold RouteSlot.main
  cw_peel
  refine ⟨?_, ?_, ?_⟩
  · clear hprods hofsSum
    intro i
    refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
      Mul.computableWitnesses env env'
    stableP_tac
  · clear hcells hofsSum
    refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
      Mul.computableWitnesses env env'
    stableP_tac
  · clear hcells hprods
    refine CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega) ?_
      Mul.computableWitnesses env env'
    stableP_tac

end RouteSlot

namespace RouteHalf

open CW

set_option maxHeartbeats 1000000 in
theorem computableWitnesses (n0 n1 n2 n3 n4 : ℕ) [NeZero n0] [NeZero n1] [NeZero n2] [NeZero n3]
    [NeZero n4] (h0 : n0 ≤ Model.ofsMax) (h1 : n1 ≤ Model.ofsMax) (h2 : n2 ≤ Model.ofsMax)
    (h3 : n3 ≤ Model.ofsMax) (h4 : n4 ≤ Model.ofsMax) :
    (RouteHalf.circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' (RouteHalf.main h0 h1 h2 h3 h4) rfl
    fun offset input env env' => ?_
  have hclaim0 : ∀ m, Stable m input input.claim0 := fun m =>
    Stable.of_eval (fun v => v.claim0) fun envX => by simp [circuit_norm]
  have hclaim1 : ∀ m, Stable m input input.claim1 := fun m =>
    Stable.of_eval (fun v => v.claim1) fun envX => by simp [circuit_norm]
  have hclaim2 : ∀ m, Stable m input input.claim2 := fun m =>
    Stable.of_eval (fun v => v.claim2) fun envX => by simp [circuit_norm]
  have hclaim3 : ∀ m, Stable m input input.claim3 := fun m =>
    Stable.of_eval (fun v => v.claim3) fun envX => by simp [circuit_norm]
  have hclaim4 : ∀ m, Stable m input input.claim4 := fun m =>
    Stable.of_eval (fun v => v.claim4) fun envX => by simp [circuit_norm]
  have hofsOH : ∀ (m j : ℕ) (hj : j < Model.ofsMax), Stable m input (input.ofsOH[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.ofsOH[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hcells0 : ∀ (m j : ℕ) (hj : j < n0), Stable m input (input.cells0[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.cells0[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hcells1 : ∀ (m j : ℕ) (hj : j < n1), Stable m input (input.cells1[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.cells1[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hcells2 : ∀ (m j : ℕ) (hj : j < n2), Stable m input (input.cells2[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.cells2[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hcells3 : ∀ (m j : ℕ) (hj : j < n3), Stable m input (input.cells3[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.cells3[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hcells4 : ∀ (m j : ℕ) (hj : j < n4), Stable m input (input.cells4[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.cells4[j]'hj) fun envX => ?_
    simp [circuit_norm]
  unfold RouteHalf.main
  cw_peel
  and_intros
  · exact CW.flat_subcircuit (RouteSlot.circuit n0 h0) input _ _ _ (by first | rfl | omega)
      (by stableP_tac) (RouteSlot.computableWitnesses n0 h0) env env'
  · exact CW.flat_subcircuit (RouteSlot.circuit n1 h1) input _ _ _ (by first | rfl | omega)
      (by stableP_tac) (RouteSlot.computableWitnesses n1 h1) env env'
  · exact CW.flat_subcircuit (RouteSlot.circuit n2 h2) input _ _ _ (by first | rfl | omega)
      (by stableP_tac) (RouteSlot.computableWitnesses n2 h2) env env'
  · exact CW.flat_subcircuit (RouteSlot.circuit n3 h3) input _ _ _ (by first | rfl | omega)
      (by stableP_tac) (RouteSlot.computableWitnesses n3 h3) env env'
  · exact CW.flat_subcircuit (RouteSlot.circuit n4 h4) input _ _ _ (by first | rfl | omega)
      (by stableP_tac) (RouteSlot.computableWitnesses n4 h4) env env'

end RouteHalf

namespace RouteCells

open CW

set_option maxHeartbeats 1000000 in
theorem computableWitnesses : (RouteCells.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' RouteCells.main rfl fun offset input env env' => ?_
  have hclaimPrev : ∀ (m j : ℕ) (hj : j < Model.nClaims),
      Stable m input (input.claimPrev[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.claimPrev[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hofsOH : ∀ (m j : ℕ) (hj : j < Model.ofsMax), Stable m input (input.ofsOH[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.ofsOH[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hiss : ∀ (m j : ℕ) (hj : j < 32), Stable m input (input.iss[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.iss[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hsub : ∀ (m j : ℕ) (hj : j < 32), Stable m input (input.sub[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.sub[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have haud : ∀ (m j : ℕ) (hj : j < 128), Stable m input (input.aud[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.aud[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hazp : ∀ (m j : ℕ) (hj : j < 128), Stable m input (input.azp[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.azp[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hhd : ∀ (m j : ℕ) (hj : j < 64), Stable m input (input.hd[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.hd[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hemail : ∀ (m j : ℕ) (hj : j < 128), Stable m input (input.email[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.email[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hnonce : ∀ (m j : ℕ) (hj : j < 64), Stable m input (input.nonce[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.nonce[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hatHash : ∀ (m j : ℕ) (hj : j < 64), Stable m input (input.atHash[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.atHash[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hiat : ∀ (m j : ℕ) (hj : j < 12), Stable m input (input.iat[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.iat[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hexp : ∀ (m j : ℕ) (hj : j < 12), Stable m input (input.exp[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.exp[j]'hj) fun envX => ?_
    simp [circuit_norm]
  unfold RouteCells.main
  cw_peel
  and_intros
  · exact CW.flat_subcircuit (RouteHalf.circuit 32 32 128 128 64 hA hA hC hC hB) input _ _ _
      (by first | rfl | omega) (by stableP_tac)
      (RouteHalf.computableWitnesses 32 32 128 128 64 hA hA hC hC hB) env env'
  · exact CW.flat_subcircuit (RouteHalf.circuit 128 64 64 12 12 hC hB hB hD hD) input _ _ _
      (by first | rfl | omega) (by stableP_tac)
      (RouteHalf.computableWitnesses 128 64 64 12 12 hC hB hB hD hD) env env'

end RouteCells

/-! ## The output slot pins -/

namespace StrSlotPin

open CW

set_option maxHeartbeats 1000000 in
theorem computableWitnesses (n : ℕ) [NeZero n] : (StrSlotPin.circuit n).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' (StrSlotPin.main n) rfl
    fun offset input env env' => ?_
  have hlen : ∀ m, Stable m input input.len := by
    intro m envA envB _ hp
    simpa [circuit_norm] using
      congrArg (fun z : StrSlotPin.Inputs n (F circomPrime) => z.len) hp
  unfold StrSlotPin.main
  cw_peel
  exact FilledMask.flat_sub (n := n) input _ _ _ _ (by first | rfl | omega) (hlen _) env env'

end StrSlotPin

namespace IntSlotPin

open CW

set_option maxHeartbeats 1000000 in
theorem computableWitnesses (n : ℕ) [NeZero n] : (IntSlotPin.circuit n).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' (IntSlotPin.main n) rfl
    fun offset input env env' => ?_
  have hlen : ∀ m, Stable m input input.len := by
    intro m envA envB _ hp
    simpa [circuit_norm] using
      congrArg (fun z : IntSlotPin.Inputs n (F circomPrime) => z.len) hp
  unfold IntSlotPin.main
  cw_peel
  exact FilledMask.flat_sub (n := n) input _ _ _ _ (by first | rfl | omega) (hlen _) env env'

end IntSlotPin

namespace BoolSlotPin

open CW

theorem computableWitnesses : (BoolSlotPin.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' BoolSlotPin.main rfl
    fun offset input env env' => ?_
  unfold BoolSlotPin.main
  cw_peel

end BoolSlotPin

/-! ## Acceptance -/

namespace Acceptance

open CW

theorem computableWitnesses : (Acceptance.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' Acceptance.main rfl fun offset input env env' => ?_
  unfold Acceptance.main
  simp only [CW.bind_iff, CW.witnessVector_iff, CW.forEach_iff, CW.assertZero_iff,
    CW.pure_iff, and_true, true_and, implies_true]
  intro _ h_input
  have hx : Expression.eval env.toEnvironment input.nMem
      = Expression.eval env'.toEnvironment input.nMem := by
    simpa [circuit_norm] using congrArg (fun z : Acceptance.Inputs (F circomPrime) => z.nMem) h_input
  -- keep the width symbolic: unifying the two evaluations at the numeral `memWidth`
  -- unrolls the whole vector and times out
  generalize memWidth = n
  exact congrArg (fun c : F circomPrime => Witgen.VExpr.eval { env := env }
    (Witgen.VExpr.range n fun i => (i =? Witgen.U64Expr.val (Witgen.FExpr.const c)).toField)) hx

end Acceptance

/-! ## The assertion-only gadgets

`Anchors`, `LenFlags` and `ClaimKinds` emit constraint rows only. -/

namespace Anchors

open CW

theorem computableWitnesses : (Anchors.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' Anchors.main rfl fun offset input env env' => ?_
  unfold Anchors.main
  simp only [CW.bind_iff, CW.forEach_iff, CW.assertZero_iff, CW.pure_iff,
    and_true, implies_true]

end Anchors

namespace LenFlags

open CW

theorem computableWitnesses : (LenFlags.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' LenFlags.main rfl fun offset input env env' => ?_
  unfold LenFlags.main
  simp only [CW.bind_iff, CW.forEach_iff, CW.assertZero_iff, CW.pure_iff,
    and_true, implies_true]

end LenFlags

namespace ClaimKinds

open CW

theorem computableWitnesses : (ClaimKinds.circuit).ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' ClaimKinds.main rfl fun offset input env env' => ?_
  unfold ClaimKinds.main
  simp only [CW.bind_iff, CW.forEach_iff, CW.assertZero_iff, and_true, implies_true]

end ClaimKinds

/-! ## Agreement of the witness-IR program

`Main`'s eleven witness sites are witness-IR programs whose only environment
reads are the input's own cells (`byteAt`, `lenE`).  `UAgree`/`FAgree`/`BAgree`/
`VAgree` say that two environments give an IR expression the same value whatever
the locals are; they are closed under every former the program uses, so the
program-level statement composes out of the definitions of `Witgen.lean` without
ever evaluating the 66578-step run. -/

namespace IRAgree

open Witgen
open IR

variable {env env' : ProverEnvironment (F circomPrime)}

/-- Two environments give the u64 expression the same value under any locals. -/
def UAgree (env env' : ProverEnvironment (F circomPrime)) (x : U64Expr (F circomPrime)) : Prop :=
  ∀ (locals : Array (F circomPrime ⊕ UInt64)) (idx : ℕ),
    U64Expr.eval ⟨env, locals, idx⟩ x = U64Expr.eval ⟨env', locals, idx⟩ x

/-- Two environments give the field expression the same value under any locals. -/
def FAgree (env env' : ProverEnvironment (F circomPrime)) (x : FExpr (F circomPrime)) : Prop :=
  ∀ (locals : Array (F circomPrime ⊕ UInt64)) (idx : ℕ),
    FExpr.eval ⟨env, locals, idx⟩ x = FExpr.eval ⟨env', locals, idx⟩ x

/-- Two environments give the condition the same value under any locals. -/
def BAgree (env env' : ProverEnvironment (F circomPrime)) (x : BExpr (F circomPrime)) : Prop :=
  ∀ (locals : Array (F circomPrime ⊕ UInt64)) (idx : ℕ),
    BExpr.eval ⟨env, locals, idx⟩ x = BExpr.eval ⟨env', locals, idx⟩ x

/-- Two environments give the vector expression the same value under any locals. -/
def VAgree {m : ℕ} (env env' : ProverEnvironment (F circomPrime)) (x : VExpr (F circomPrime) m) :
    Prop :=
  ∀ (locals : Array (F circomPrime ⊕ UInt64)) (idx : ℕ),
    VExpr.eval ⟨env, locals, idx⟩ x = VExpr.eval ⟨env', locals, idx⟩ x

/-! ### The formers -/

theorem UAgree.const (n : UInt64) : UAgree env env' (.const n) := fun _ _ => rfl

theorem UAgree.idx : UAgree env env' .idx := fun _ _ => rfl

theorem UAgree.localVar (i : ℕ) : UAgree env env' (.localVar i) := fun _ _ => rfl

theorem UAgree.val {x : FExpr (F circomPrime)} (h : FAgree env env' x) :
    UAgree env env' (.val x) := by
  intro locals idx
  simp only [U64Expr.eval, h locals idx]

theorem UAgree.add {x y : U64Expr (F circomPrime)} (hx : UAgree env env' x)
    (hy : UAgree env env' y) : UAgree env env' (.add x y) := by
  intro locals idx
  simp only [U64Expr.eval, hx locals idx, hy locals idx]

theorem UAgree.mul {x y : U64Expr (F circomPrime)} (hx : UAgree env env' x)
    (hy : UAgree env env' y) : UAgree env env' (.mul x y) := by
  intro locals idx
  simp only [U64Expr.eval, hx locals idx, hy locals idx]

theorem UAgree.div {x y : U64Expr (F circomPrime)} (hx : UAgree env env' x)
    (hy : UAgree env env' y) : UAgree env env' (.div x y) := by
  intro locals idx
  simp only [U64Expr.eval, hx locals idx, hy locals idx]

theorem UAgree.mod {x y : U64Expr (F circomPrime)} (hx : UAgree env env' x)
    (hy : UAgree env env' y) : UAgree env env' (.mod x y) := by
  intro locals idx
  simp only [U64Expr.eval, hx locals idx, hy locals idx]

theorem UAgree.ite {c : BExpr (F circomPrime)} {x y : U64Expr (F circomPrime)}
    (hc : BAgree env env' c) (hx : UAgree env env' x) (hy : UAgree env env' y) :
    UAgree env env' (.ite c x y) := by
  intro locals idx
  simp only [U64Expr.eval, hc locals idx, hx locals idx, hy locals idx]

theorem FAgree.const (c : F circomPrime) : FAgree env env' (.const c) := fun _ _ => rfl

theorem FAgree.localVar (i : ℕ) : FAgree env env' (.localVar i) := fun _ _ => rfl

theorem FAgree.expr {e : Expression (F circomPrime)}
    (h : Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e) :
    FAgree env env' (.expr e) := fun _ _ => h

theorem FAgree.add {x y : FExpr (F circomPrime)} (hx : FAgree env env' x)
    (hy : FAgree env env' y) : FAgree env env' (.add x y) := by
  intro locals idx
  simp only [FExpr.eval, hx locals idx, hy locals idx]

theorem FAgree.mul {x y : FExpr (F circomPrime)} (hx : FAgree env env' x)
    (hy : FAgree env env' y) : FAgree env env' (.mul x y) := by
  intro locals idx
  simp only [FExpr.eval, hx locals idx, hy locals idx]

theorem FAgree.inv {x : FExpr (F circomPrime)} (hx : FAgree env env' x) :
    FAgree env env' (.inv x) := by
  intro locals idx
  simp only [FExpr.eval, hx locals idx]

theorem FAgree.ofU64 {x : U64Expr (F circomPrime)} (hx : UAgree env env' x) :
    FAgree env env' (.ofU64 x) := by
  intro locals idx
  simp only [FExpr.eval, hx locals idx]

theorem FAgree.ite {c : BExpr (F circomPrime)} {x y : FExpr (F circomPrime)}
    (hc : BAgree env env' c) (hx : FAgree env env' x) (hy : FAgree env env' y) :
    FAgree env env' (.ite c x y) := by
  intro locals idx
  simp only [FExpr.eval, hc locals idx, hx locals idx, hy locals idx]

theorem FAgree.evalList {xs : List (FExpr (F circomPrime))}
    (hxs : ∀ x ∈ xs, FAgree env env' x) (locals : Array (F circomPrime ⊕ UInt64)) (idx : ℕ) :
    ∀ k, FExpr.evalList ⟨env, locals, idx⟩ k xs = FExpr.evalList ⟨env', locals, idx⟩ k xs := by
  induction xs with
  | nil => intro k; cases k <;> rfl
  | cons a as ih =>
    intro k
    cases k with
    | zero =>
      simp only [FExpr.evalList]
      exact hxs a (List.mem_cons_self ..) locals idx
    | succ k =>
      simp only [FExpr.evalList]
      exact ih (fun x hx => hxs x (List.mem_cons_of_mem _ hx)) k

theorem FAgree.listGet {xs : List (FExpr (F circomPrime))} {i : U64Expr (F circomPrime)}
    (hxs : ∀ x ∈ xs, FAgree env env' x) (hi : UAgree env env' i) :
    FAgree env env' (.listGet xs i) := by
  intro locals idx
  simp only [FExpr.eval, hi locals idx]
  exact FAgree.evalList hxs locals idx _

theorem BAgree.true : BAgree env env' .true := fun _ _ => rfl

theorem BAgree.false : BAgree env env' .false := fun _ _ => rfl

theorem BAgree.neq {x y : U64Expr (F circomPrime)} (hx : UAgree env env' x)
    (hy : UAgree env env' y) : BAgree env env' (.neq x y) := by
  intro locals idx
  simp only [BExpr.eval, hx locals idx, hy locals idx]

theorem BAgree.lt {x y : U64Expr (F circomPrime)} (hx : UAgree env env' x)
    (hy : UAgree env env' y) : BAgree env env' (.lt x y) := by
  intro locals idx
  simp only [BExpr.eval, hx locals idx, hy locals idx]

theorem BAgree.not {c : BExpr (F circomPrime)} (hc : BAgree env env' c) :
    BAgree env env' (.not c) := by
  intro locals idx
  simp only [BExpr.eval, hc locals idx]

theorem BAgree.and {x y : BExpr (F circomPrime)} (hx : BAgree env env' x)
    (hy : BAgree env env' y) : BAgree env env' (.and x y) := by
  intro locals idx
  simp only [BExpr.eval, hx locals idx, hy locals idx]

theorem VAgree.lit {m : ℕ} {es : Vector (FExpr (F circomPrime)) m}
    (h : ∀ (j : ℕ) (hj : j < m), FAgree env env' (es[j]'hj)) : VAgree env env' (.lit es) := by
  intro locals idx
  simp only [VExpr.eval]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map]
  exact h j hj locals idx

theorem VAgree.mapRange {m : ℕ} {body : FExpr (F circomPrime)} (h : FAgree env env' body) :
    VAgree env env' (.mapRange m body) := by
  intro locals idx
  simp only [VExpr.eval]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_mapRange]
  exact h locals j

/-! ### The `Witgen.lean` combinators -/

theorem cst_agree (n : ℕ) : UAgree env env' (IR.cst n) := UAgree.const _

theorem toU_agree {c : BExpr (F circomPrime)} (h : BAgree env env' c) :
    UAgree env env' (IR.toU c) :=
  UAgree.ite h (cst_agree _) (cst_agree _)

theorem toF_agree {c : BExpr (F circomPrime)} (h : BAgree env env' c) :
    FAgree env env' (IR.toF c) :=
  FAgree.ite h (FAgree.const _) (FAgree.const _)

theorem bor_agree {x y : BExpr (F circomPrime)} (hx : BAgree env env' x) (hy : BAgree env env' y) :
    BAgree env env' (IR.bor x y) :=
  BAgree.not (BAgree.and (BAgree.not hx) (BAgree.not hy))

theorem eqn_agree {x : U64Expr (F circomPrime)} (hx : UAgree env env' x) (n : ℕ) :
    BAgree env env' (IR.eqn x n) :=
  BAgree.neq hx (cst_agree _)

theorem leN_agree {x : U64Expr (F circomPrime)} (hx : UAgree env env' x) (n : ℕ) :
    BAgree env env' (IR.leN x n) :=
  BAgree.not (BAgree.lt (cst_agree _) hx)

theorem geN_agree {x : U64Expr (F circomPrime)} (hx : UAgree env env' x) (n : ℕ) :
    BAgree env env' (IR.geN x n) :=
  BAgree.not (BAgree.lt hx (cst_agree _))

theorem rngN_agree {x : U64Expr (F circomPrime)} (hx : UAgree env env' x) (lo hi : ℕ) :
    BAgree env env' (IR.rngN x lo hi) :=
  BAgree.and (geN_agree hx _) (leN_agree hx _)

theorem subN_agree {x : U64Expr (F circomPrime)} (hx : UAgree env env' x) (n : ℕ) :
    UAgree env env' (IR.subN x n) :=
  UAgree.add hx (UAgree.const _)

theorem minN_agree {x : U64Expr (F circomPrime)} (hx : UAgree env env' x) (n : ℕ) :
    UAgree env env' (IR.minN x n) :=
  UAgree.ite (BAgree.lt (cst_agree _) hx) (cst_agree _) hx

theorem anyEq_agree {x : U64Expr (F circomPrime)} (hx : UAgree env env' x) :
    ∀ ns : List ℕ, BAgree env env' (IR.anyEq x ns)
  | [] => BAgree.false
  | [_] => eqn_agree hx _
  | _ :: _ :: _ => bor_agree (eqn_agree hx _) (anyEq_agree hx _)

/-- Agreement of every branch of a decision chain.  This is a recursive predicate
rather than `∀ p ∈ ds, …`: `∈` goes through `Membership`'s `outParam`, and on a
27-branch chain resolving that dominates every other cost. -/
def ChainOk (env env' : ProverEnvironment (F circomPrime)) :
    List (BExpr (F circomPrime) × U64Expr (F circomPrime)) → Prop
  | [] => True
  | p :: ds => BAgree env env' p.1 ∧ UAgree env env' p.2 ∧ ChainOk env env' ds

theorem chain_agree {dflt : U64Expr (F circomPrime)} (hd : UAgree env env' dflt) :
    ∀ ds : List (BExpr (F circomPrime) × U64Expr (F circomPrime)),
      ChainOk env env' ds → UAgree env env' (IR.chain ds dflt)
  | [], _ => hd
  | p :: ps, h => by
      rw [IR.chain, List.foldr_cons]
      exact UAgree.ite h.1 h.2.1 (chain_agree hd ps h.2.2)

theorem reg_agree (i off : ℕ) : UAgree env env' (IR.reg i off) := UAgree.localVar _

theorem sigl_agree (i off : ℕ) : UAgree env env' (IR.sigl i off) := UAgree.localVar _


/-! ### The byte classes and the table read-outs -/

theorem cWs_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cWs b) := anyEq_agree h _

theorem cDigit_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cDigit b) := rngN_agree h _ _

theorem cDigitNz_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cDigitNz b) := rngN_agree h _ _

theorem cUpperHex_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cUpperHex b) := rngN_agree h _ _

theorem cLowerHex_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cLowerHex b) := rngN_agree h _ _

theorem cHex_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cHex b) :=
  bor_agree (cDigit_agree h) (bor_agree (cUpperHex_agree h) (cLowerHex_agree h))

theorem cUnesc_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cUnesc b) :=
  BAgree.and (rngN_agree h _ _)
    (BAgree.and (BAgree.not (eqn_agree h _)) (BAgree.not (eqn_agree h _)))

theorem cExpL_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cExpL b) := bor_agree (eqn_agree h _) (eqn_agree h _)

theorem cSign_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cSign b) := bor_agree (eqn_agree h _) (eqn_agree h _)

theorem cSimpleEsc_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cSimpleEsc b) := anyEq_agree h _

theorem cCont_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cCont b) := rngN_agree h _ _

theorem cLead2_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cLead2 b) := rngN_agree h _ _

theorem cLead3_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cLead3 b) := bor_agree (rngN_agree h _ _) (rngN_agree h _ _)

theorem cLead4_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cLead4 b) := rngN_agree h _ _

theorem cA0BF_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.cA0BF b) := rngN_agree h _ _

theorem c809F_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.c809F b) := rngN_agree h _ _

theorem c90BF_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.c90BF b) := rngN_agree h _ _

theorem c808F_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    BAgree env env' (IR.c808F b) := rngN_agree h _ _

theorem escValE_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    UAgree env env' (IR.escValE b) := by
  refine chain_agree (cst_agree _) _ ?_
  exact ⟨eqn_agree h _, cst_agree _, eqn_agree h _, cst_agree _, eqn_agree h _, cst_agree _,
    eqn_agree h _, cst_agree _, eqn_agree h _, cst_agree _, eqn_agree h _, cst_agree _,
    eqn_agree h _, cst_agree _, eqn_agree h _, cst_agree _, trivial⟩

theorem hexValE_agree {b : U64Expr (F circomPrime)} (h : UAgree env env' b) :
    UAgree env env' (IR.hexValE b) := by
  refine chain_agree (cst_agree _) _ ?_
  exact ⟨cDigit_agree h, subN_agree h _, cUpperHex_agree h, subN_agree h _,
    cLowerHex_agree h, subN_agree h _, trivial⟩

theorem kindE_agree {c : U64Expr (F circomPrime)} (h : UAgree env env' c) :
    UAgree env env' (IR.kindE c) := by
  unfold IR.kindE
  generalize (List.finRange Model.nClaims) = L
  induction L with
  | nil => exact cst_agree _
  | cons k ks ih =>
    rw [List.foldr_cons]
    exact UAgree.ite (eqn_agree h _) (cst_agree _) ih

theorem capE_agree {c : U64Expr (F circomPrime)} (h : UAgree env env' c) :
    UAgree env env' (IR.capE c) := by
  unfold IR.capE
  generalize (List.finRange Model.nClaims) = L
  induction L with
  | nil => exact cst_agree _
  | cons k ks ih =>
    rw [List.foldr_cons]
    exact UAgree.ite (eqn_agree h _) (cst_agree _) ih

theorem nameAtE_agree (k : Model.Claim) {x : U64Expr (F circomPrime)} (h : UAgree env env' x) :
    UAgree env env' (IR.nameAtE k x) := by
  refine UAgree.val (FAgree.listGet ?_ h)
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨z, -, rfl⟩ := hy
  exact FAgree.const _

/-- Membership form of `VAgree.lit`. -/
theorem VAgree.lit_mem {m : ℕ} {es : Vector (FExpr (F circomPrime)) m}
    (h : ∀ x ∈ es, FAgree env env' x) : VAgree env env' (.lit es) := by
  intro locals idx
  simp only [VExpr.eval]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map]
  exact h _ (Vector.getElem_mem hj) locals idx

theorem countE_agree (off k : ℕ) : FAgree env env' (IR.countE off k) := by
  unfold IR.countE
  generalize (List.range bufferLen) = L
  induction L with
  | nil => exact FAgree.const _
  | cons i is ih =>
    rw [List.foldr_cons]
    exact FAgree.add (toF_agree (BAgree.neq (sigl_agree _ _) (cst_agree _))) ih

theorem cellE_agree (c : ℕ) : FAgree env env' (IR.cellE c) := by
  unfold IR.cellE
  generalize (List.range bufferLen) = L
  induction L with
  | nil => exact FAgree.const _
  | cons i is ih =>
    rw [List.foldr_cons]
    exact FAgree.ite (BAgree.neq (sigl_agree _ _) (cst_agree _))
      (FAgree.ofU64 (sigl_agree _ _)) ih

theorem natOut_agree (off : ℕ) : VAgree env env' (IR.natOut off) := by
  unfold IR.natOut
  refine VAgree.lit fun j hj => ?_
  simp only [Vector.getElem_ofFn]
  exact FAgree.ofU64 (reg_agree _ _)

theorem stOut_agree : VAgree env env' IR.stOut := by
  unfold IR.stOut
  refine VAgree.lit fun j hj => ?_
  simp only [Vector.getElem_ofFn]
  exact toF_agree (BAgree.neq (reg_agree _ _) (cst_agree _))

theorem subOut_agree : VAgree env env' IR.subOut := by
  unfold IR.subOut
  refine VAgree.lit fun j hj => ?_
  simp only [Vector.getElem_ofFn]
  exact toF_agree (BAgree.neq (reg_agree _ _) (cst_agree _))

theorem mOut_agree : VAgree env env' IR.mOut := by
  unfold IR.mOut
  refine VAgree.lit fun j hj => ?_
  simp only [Vector.getElem_ofFn]
  exact toF_agree (BAgree.neq (reg_agree _ _) (cst_agree _))

theorem claimOut_agree : VAgree env env' IR.claimOut := by
  unfold IR.claimOut
  refine VAgree.lit fun j hj => ?_
  simp only [Vector.getElem_ofFn]
  exact toF_agree (BAgree.neq (reg_agree _ _) (cst_agree _))


/-! ### Steps and the program -/

/-- A `let`-step of the program agrees. -/
def StepAgree (env env' : ProverEnvironment (F circomPrime)) : Step (F circomPrime) → Prop
  | .letF e => FAgree env env' e
  | .letU e => UAgree env env' e

/-- Every step of a straight-line program agrees.  This is a recursive predicate
rather than `∀ s ∈ steps, …`: `∈` goes through `Membership`'s `outParam`, and on a
program this size resolving that dominates every other cost. -/
def StepsAgree (env env' : ProverEnvironment (F circomPrime)) :
    List (Step (F circomPrime)) → Prop
  | [] => True
  | s :: ss => StepAgree env env' s ∧ StepsAgree env env' ss

theorem StepsAgree.append {a b : List (Step (F circomPrime))}
    (ha : StepsAgree env env' a) (hb : StepsAgree env env' b) :
    StepsAgree env env' (a ++ b) := by
  induction a with
  | nil => exact hb
  | cons s ss ih => exact ⟨ha.1, ih ha.2⟩

theorem StepsAgree.flatMap {α : Type} (f : α → List (Step (F circomPrime))) (l : List α)
    (h : ∀ a, StepsAgree env env' (f a)) : StepsAgree env env' (l.flatMap f) := by
  induction l with
  | nil => exact trivial
  | cons a as ih => exact (h a).append ih

theorem StepsAgree.replicate (s : Step (F circomPrime)) (n : ℕ) (h : StepAgree env env' s) :
    StepsAgree env env' (List.replicate n s) := by
  induction n with
  | zero => exact trivial
  | succ n ih => exact ⟨h, ih⟩

/-- Two environments that agree on every step's expression run the whole
straight-line program to the same locals. -/
theorem evalSteps_congr (steps : List (Step (F circomPrime)))
    (h : StepsAgree env env' steps) :
    ∀ locals : Array (F circomPrime ⊕ UInt64),
      evalSteps env steps locals = evalSteps env' steps locals := by
  induction steps with
  | nil => intro locals; rfl
  | cons s steps ih =>
    intro locals
    cases s with
    | letF e =>
      simp only [evalSteps]
      rw [show FExpr.eval { env := env, locals := locals } e
          = FExpr.eval { env := env', locals := locals } e from h.1 locals 0]
      exact ih h.2 _
    | letU e =>
      simp only [evalSteps]
      rw [show U64Expr.eval { env := env, locals := locals } e
          = U64Expr.eval { env := env', locals := locals } e from h.1 locals 0]
      exact ih h.2 _

theorem initBlock_agree : StepsAgree env env' IR.initBlock := by
  unfold IR.initBlock
  refine StepsAgree.append ?_
    (StepsAgree.replicate (Step.letU (IR.cst 0)) Model.nClaims (UAgree.const _))
  exact ⟨UAgree.const _, UAgree.const _, UAgree.const _, UAgree.const _, UAgree.const _,
    UAgree.const _, UAgree.const _, trivial⟩

/-- A witness-IR program whose steps and output only read the input. -/
theorem eval_ir_congr {m : ℕ} (steps : List (Step (F circomPrime)))
    (out : VExpr (F circomPrime) m) (hsteps : StepsAgree env env' steps)
    (hout : VAgree env env' out) :
    (WitgenIR.ir steps out).eval env = (WitgenIR.ir steps out).eval env' := by
  show out.eval { env := env, locals := evalSteps env steps }
    = out.eval { env := env', locals := evalSteps env' steps }
  rw [evalSteps_congr steps hsteps]
  exact hout _ _

theorem lenFlagsOut_agree (input : Var Input (F circomPrime))
    (hlen : Expression.eval env.toEnvironment input.len
      = Expression.eval env'.toEnvironment input.len) :
    VAgree env env' (IR.lenFlagsOut input) :=
  VAgree.mapRange (toF_agree (BAgree.neq UAgree.idx (UAgree.val (FAgree.expr hlen))))

theorem accmOut_agree (input : Var Input (F circomPrime))
    (hlen : Expression.eval env.toEnvironment input.len
      = Expression.eval env'.toEnvironment input.len) :
    VAgree env env' (IR.accmOut input) :=
  VAgree.mapRange (toF_agree (BAgree.lt (UAgree.val (FAgree.expr hlen)) UAgree.idx))

theorem byteAt_agree (input : Var Input (F circomPrime)) (i : ℕ)
    (hbuf : ∀ (j : ℕ) (hj : j < bufferLen),
      Expression.eval env.toEnvironment (input.buffer[j]'hj)
        = Expression.eval env'.toEnvironment (input.buffer[j]'hj)) :
    FAgree env env' (IR.byteAt input i) := by
  refine FAgree.expr ?_
  by_cases h : i < bufferLen
  · rw [dif_pos h]
    exact hbuf i h
  · rw [dif_neg h]
    rfl

theorem lenE_agree (input : Var Input (F circomPrime))
    (hlen : Expression.eval env.toEnvironment input.len
      = Expression.eval env'.toEnvironment input.len) :
    UAgree env env' (IR.lenE input) := UAgree.val (FAgree.expr hlen)

/-! ### One position block

`IR.stepBlock` is 65 `letU`s built from the combinators above.  The proof
normalises the block to raw IR constructors with a single `simp only` (the
combinator definitions plus `List.foldr`, which is a linear pass), generalises
the one list the program folds over (`List.finRange nClaims`: leaving it
concrete makes every failed unification `whnf` it), and then walks the resulting
term with a *reducible* search.  `with_reducible` is what makes the search
affordable: at default transparency a failed alternative unfolds `UAgree` /
`StepsAgree` / the folds and the search does not terminate, while at reducible
transparency every alternative is matched on the head constructor and fails in
constant time. -/

theorem StepsAgree.nil : StepsAgree env env' [] := trivial

theorem StepsAgree.cons {s : Step (F circomPrime)} {ss : List (Step (F circomPrime))}
    (h : StepAgree env env' s) (hs : StepsAgree env env' ss) :
    StepsAgree env env' (s :: ss) := ⟨h, hs⟩

theorem StepAgree.letU {e : U64Expr (F circomPrime)} (h : UAgree env env' e) :
    StepAgree env env' (.letU e) := h

theorem StepAgree.letF {e : FExpr (F circomPrime)} (h : FAgree env env' e) :
    StepAgree env env' (.letF e) := h

theorem StepsAgree.map {α : Type} (f : α → Step (F circomPrime)) (l : List α)
    (h : ∀ a, StepAgree env env' (f a)) : StepsAgree env env' (l.map f) := by
  induction l with
  | nil => exact trivial
  | cons a as ih => exact ⟨h a, ih⟩

/-- A decision chain folded over an abstract list (`kindE`, `capE`, the
claim-matching cascade).  Stated over the list so that the search never has to
evaluate `List.finRange nClaims`. -/
theorem foldrIte_agree {α : Type} (c : α → BExpr (F circomPrime))
    (v : α → U64Expr (F circomPrime)) (dflt : U64Expr (F circomPrime))
    (hc : ∀ a, BAgree env env' (c a)) (hv : ∀ a, UAgree env env' (v a))
    (hd : UAgree env env' dflt) :
    ∀ l : List α, UAgree env env' (l.foldr (fun a acc => .ite (c a) (v a) acc) dflt)
  | [] => hd
  | a :: as => UAgree.ite (hc a) (hv a) (foldrIte_agree c v dflt hc hv hd as)

/-- Walk a block of the program that has been normalised to raw IR constructors.
Every alternative is head-matched at *reducible* transparency, so a failure costs
one constructor comparison. -/
syntax "ir_agree_search" : tactic
macro_rules
  | `(tactic| ir_agree_search) => `(tactic|
      repeat' with_reducible first
        | apply StepsAgree.cons
        | apply StepAgree.letU
        | exact UAgree.localVar _
        | exact UAgree.const _
        | apply BAgree.neq
        | apply BAgree.not
        | apply BAgree.and
        | apply BAgree.lt
        | apply UAgree.ite
        | apply UAgree.add
        | apply UAgree.mul
        | apply UAgree.val
        | exact FAgree.const _
        | apply FAgree.ite
        | apply FAgree.ofU64
        | assumption
        | apply nameAtE_agree
        | refine foldrIte_agree _ _ _ (fun _ => ?_) (fun _ => ?_) ?_ _
        | exact StepsAgree.nil)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem stepBlock_agree (input : Var Input (F circomPrime)) (i : ℕ)
    (hbuf : ∀ (j : ℕ) (hj : j < bufferLen),
      Expression.eval env.toEnvironment (input.buffer[j]'hj)
        = Expression.eval env'.toEnvironment (input.buffer[j]'hj))
    (hlen : Expression.eval env.toEnvironment input.len
      = Expression.eval env'.toEnvironment input.len) :
    StepsAgree env env' (IR.stepBlock input i) := by
  have hb : FAgree env env' (IR.byteAt input i) := byteAt_agree input i hbuf
  have hl : UAgree env env' (IR.lenE input) := lenE_agree input hlen
  simp only [IR.stepBlock, IR.cst, IR.bor, IR.toU, IR.eqn, IR.leN, IR.geN, IR.rngN,
    IR.subN, IR.minN, IR.anyEq, IR.chain, IR.reg, IR.sigl, IR.cWs, IR.cDigit, IR.cDigitNz,
    IR.cUpperHex, IR.cLowerHex, IR.cHex, IR.cUnesc, IR.cExpL, IR.cSign, IR.cSimpleEsc,
    IR.cCont, IR.cLead2, IR.cLead3, IR.cLead4, IR.cA0BF, IR.c809F, IR.c90BF, IR.c808F,
    IR.escValE, IR.hexValE, IR.kindE, IR.capE,
    List.foldr_cons, List.foldr_nil]
  generalize List.finRange Model.nClaims = L
  refine StepsAgree.append ?_ (StepsAgree.map _ _ ?_)
  case _ => ir_agree_search
  case _ => refine fun k => ?_; ir_agree_search

set_option maxRecDepth 8000 in
theorem runSteps_agree (input : Var Input (F circomPrime))
    (hbuf : ∀ (j : ℕ) (hj : j < bufferLen),
      Expression.eval env.toEnvironment (input.buffer[j]'hj)
        = Expression.eval env'.toEnvironment (input.buffer[j]'hj))
    (hlen : Expression.eval env.toEnvironment input.len
      = Expression.eval env'.toEnvironment input.len) :
    StepsAgree env env' (IR.runSteps input) := by
  unfold IR.runSteps IR.stepsUpTo
  refine initBlock_agree.append (StepsAgree.flatMap _ _ fun i => ?_)
  exact stepBlock_agree input i hbuf hlen

/-! ### The output read-out

`outLit` is the `toElements` of a struct of `countE` / `cellE` read-outs, which
are layout-only.  Going through the struct (rather than the 664-cell element
vector) keeps the proof at the level of the eleven slots. -/

theorem strSlotE_agree (k n : ℕ) (locals : Array (F circomPrime ⊕ UInt64)) (idx : ℕ) :
    Witgen.eval (M := StrSlot n) ⟨env, locals, idx⟩ (IR.strSlotE k n)
      = Witgen.eval (M := StrSlot n) ⟨env', locals, idx⟩ (IR.strSlotE k n) := by
  simp only [IR.strSlotE]
  rw [IR.eval_strSlot, IR.eval_strSlot]
  simp only [StrSlot.mk.injEq]
  refine ⟨countE_agree _ _ locals idx, countE_agree _ _ locals idx, ?_⟩
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  exact cellE_agree _ locals idx

theorem intSlotE_agree (k n : ℕ) (locals : Array (F circomPrime ⊕ UInt64)) (idx : ℕ) :
    Witgen.eval (M := IntSlot n) ⟨env, locals, idx⟩ (IR.intSlotE k n)
      = Witgen.eval (M := IntSlot n) ⟨env', locals, idx⟩ (IR.intSlotE k n) := by
  simp only [IR.intSlotE]
  rw [IR.eval_intSlot, IR.eval_intSlot]
  simp only [IntSlot.mk.injEq]
  refine ⟨countE_agree _ _ locals idx, countE_agree _ _ locals idx,
    countE_agree _ _ locals idx, ?_⟩
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  exact cellE_agree _ locals idx

theorem boolSlotE_agree (k : ℕ) (locals : Array (F circomPrime ⊕ UInt64)) (idx : ℕ) :
    Witgen.eval (M := BoolSlot) ⟨env, locals, idx⟩ (IR.boolSlotE k)
      = Witgen.eval (M := BoolSlot) ⟨env', locals, idx⟩ (IR.boolSlotE k) := by
  simp only [IR.boolSlotE]
  rw [IR.eval_boolSlot, IR.eval_boolSlot]
  simp only [BoolSlot.mk.injEq]
  exact ⟨countE_agree _ _ locals idx, countE_agree _ _ locals idx⟩

theorem outStruct_agree (locals : Array (F circomPrime ⊕ UInt64)) (idx : ℕ) :
    Witgen.eval (M := Output) ⟨env, locals, idx⟩ IR.outStruct
      = Witgen.eval (M := Output) ⟨env', locals, idx⟩ IR.outStruct := by
  rw [IR.eval_output, IR.eval_output]
  simp only [IR.outStruct, Output.mk.injEq]
  exact ⟨strSlotE_agree _ _ _ _, strSlotE_agree _ _ _ _, strSlotE_agree _ _ _ _,
    strSlotE_agree _ _ _ _, strSlotE_agree _ _ _ _, strSlotE_agree _ _ _ _,
    boolSlotE_agree _ _ _, strSlotE_agree _ _ _ _, strSlotE_agree _ _ _ _,
    intSlotE_agree _ _ _ _, intSlotE_agree _ _ _ _⟩

theorem outLit_agree : VAgree env env' IR.outLit := by
  intro locals idx
  have h := congrArg ProvableType.toElements
    (outStruct_agree (env := env) (env' := env') locals idx)
  rw [Witgen.eval, Witgen.eval, ProvableType.toElements_fromElements,
    ProvableType.toElements_fromElements] at h
  show VExpr.eval _ IR.outLit = VExpr.eval _ IR.outLit
  unfold IR.outLit
  simpa only [VExpr.eval] using h

theorem hexAccOut_agree : VAgree env env' IR.hexAccOut := by
  unfold IR.hexAccOut; exact natOut_agree _

theorem kIdxOut_agree : VAgree env env' IR.kIdxOut := by
  unfold IR.kIdxOut; exact natOut_agree _

theorem ofsOut_agree : VAgree env env' IR.ofsOut := by
  unfold IR.ofsOut; exact natOut_agree _

theorem nMemOut_agree : VAgree env env' IR.nMemOut := by
  unfold IR.nMemOut; exact natOut_agree _

/-! ### The eleven witness sites of `Main` -/

section Sites

variable (input : Var Input (F circomPrime))
  (hbuf : ∀ (j : ℕ) (hj : j < bufferLen),
    Expression.eval env.toEnvironment (input.buffer[j]'hj)
      = Expression.eval env'.toEnvironment (input.buffer[j]'hj))
  (hlen : Expression.eval env.toEnvironment input.len
    = Expression.eval env'.toEnvironment input.len)

include hbuf hlen

theorem stIR_agree : (IR.stIR input).eval env = (IR.stIR input).eval env' := by
  unfold IR.stIR
  exact eval_ir_congr _ _ (runSteps_agree input hbuf hlen) stOut_agree

theorem subIR_agree : (IR.subIR input).eval env = (IR.subIR input).eval env' := by
  unfold IR.subIR
  exact eval_ir_congr _ _ (runSteps_agree input hbuf hlen) subOut_agree

theorem mIR_agree : (IR.mIR input).eval env = (IR.mIR input).eval env' := by
  unfold IR.mIR
  exact eval_ir_congr _ _ (runSteps_agree input hbuf hlen) mOut_agree

theorem claimIR_agree : (IR.claimIR input).eval env = (IR.claimIR input).eval env' := by
  unfold IR.claimIR
  exact eval_ir_congr _ _ (runSteps_agree input hbuf hlen) claimOut_agree

theorem hexAccIR_agree : (IR.hexAccIR input).eval env = (IR.hexAccIR input).eval env' := by
  unfold IR.hexAccIR
  exact eval_ir_congr _ _ (runSteps_agree input hbuf hlen) hexAccOut_agree

theorem kIdxIR_agree : (IR.kIdxIR input).eval env = (IR.kIdxIR input).eval env' := by
  unfold IR.kIdxIR
  exact eval_ir_congr _ _ (runSteps_agree input hbuf hlen) kIdxOut_agree

theorem ofsIR_agree : (IR.ofsIR input).eval env = (IR.ofsIR input).eval env' := by
  unfold IR.ofsIR
  exact eval_ir_congr _ _ (runSteps_agree input hbuf hlen) ofsOut_agree

theorem nMemIR_agree : (IR.nMemIR input).eval env = (IR.nMemIR input).eval env' := by
  unfold IR.nMemIR
  exact eval_ir_congr _ _ (runSteps_agree input hbuf hlen) nMemOut_agree

theorem outIR_agree : (IR.outIR input).eval env = (IR.outIR input).eval env' := by
  unfold IR.outIR
  exact eval_ir_congr _ _ (runSteps_agree input hbuf hlen) outLit_agree

omit hbuf in
theorem lenFlagsOut_eval_agree :
    (IR.lenFlagsOut input).eval { env := env } = (IR.lenFlagsOut input).eval { env := env' } :=
  lenFlagsOut_agree input hlen _ _

omit hbuf in
theorem accmOut_eval_agree :
    (IR.accmOut input).eval { env := env } = (IR.accmOut input).eval { env := env' } :=
  accmOut_agree input hlen _ _

end Sites

end IRAgree

/-! ## One position -/

namespace Step

open CW

set_option maxHeartbeats 1000000 in
theorem computableWitnesses : (Step.circuit).base.ComputableWitnesses := by
  refine CW.computableWitnesses_of_structural' Step.main rfl fun offset input env env' => ?_
  have hbyte : ∀ m, Stable m input input.byte := fun m =>
    Stable.of_eval (fun v => v.byte) fun envX => by simp [circuit_norm]
  have hlenFlag : ∀ m, Stable m input input.lenFlag := fun m =>
    Stable.of_eval (fun v => v.lenFlag) fun envX => by simp [circuit_norm]
  have haccmPrev : ∀ m, Stable m input input.accmPrev := fun m =>
    Stable.of_eval (fun v => v.accmPrev) fun envX => by simp [circuit_norm]
  have haccmNext : ∀ m, Stable m input input.accmNext := fun m =>
    Stable.of_eval (fun v => v.accmNext) fun envX => by simp [circuit_norm]
  have hhexAccPrev : ∀ m, Stable m input input.hexAccPrev := fun m =>
    Stable.of_eval (fun v => v.hexAccPrev) fun envX => by simp [circuit_norm]
  have hhexAccNext : ∀ m, Stable m input input.hexAccNext := fun m =>
    Stable.of_eval (fun v => v.hexAccNext) fun envX => by simp [circuit_norm]
  have hkIdxPrev : ∀ m, Stable m input input.kIdxPrev := fun m =>
    Stable.of_eval (fun v => v.kIdxPrev) fun envX => by simp [circuit_norm]
  have hkIdxNext : ∀ m, Stable m input input.kIdxNext := fun m =>
    Stable.of_eval (fun v => v.kIdxNext) fun envX => by simp [circuit_norm]
  have hofsPrev : ∀ m, Stable m input input.ofsPrev := fun m =>
    Stable.of_eval (fun v => v.ofsPrev) fun envX => by simp [circuit_norm]
  have hofsNext : ∀ m, Stable m input input.ofsNext := fun m =>
    Stable.of_eval (fun v => v.ofsNext) fun envX => by simp [circuit_norm]
  have hnMemPrev : ∀ m, Stable m input input.nMemPrev := fun m =>
    Stable.of_eval (fun v => v.nMemPrev) fun envX => by simp [circuit_norm]
  have hnMemNext : ∀ m, Stable m input input.nMemNext := fun m =>
    Stable.of_eval (fun v => v.nMemNext) fun envX => by simp [circuit_norm]
  have hstPrev : ∀ (m j : ℕ) (hj : j < Model.nSt), Stable m input (input.stPrev[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.stPrev[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hstNext : ∀ (m j : ℕ) (hj : j < Model.nSt), Stable m input (input.stNext[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.stNext[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hsubPrev : ∀ (m j : ℕ) (hj : j < Model.nSub), Stable m input (input.subPrev[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.subPrev[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hsubNext : ∀ (m j : ℕ) (hj : j < Model.nSub), Stable m input (input.subNext[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.subNext[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hmPrev : ∀ (m j : ℕ) (hj : j < Model.nClaims), Stable m input (input.mPrev[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.mPrev[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hmNext : ∀ (m j : ℕ) (hj : j < Model.nClaims), Stable m input (input.mNext[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.mNext[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hclaimPrev : ∀ (m j : ℕ) (hj : j < Model.nClaims), Stable m input (input.claimPrev[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.claimPrev[j]'hj) fun envX => ?_
    simp [circuit_norm]
  have hclaimNext : ∀ (m j : ℕ) (hj : j < Model.nClaims), Stable m input (input.claimNext[j]'hj) := by
    intro m j hj
    refine Stable.of_eval (fun v => v.claimNext[j]'hj) fun envX => ?_
    simp [circuit_norm]
  unfold Step.main Rows.mul
  cw_peel! [CW.sub_localLength, CW.subWithAssertion_localLength, CW.assertion_localLength,
    byteClass_localLength, claimKinds_localLength, emit_localLength, codePoint_localLength,
    keyIndex_localLength, keyMatchers_localLength, claimReg_localLength, valueEmit_localLength,
    offset_localLength, claimSignals_localLength, routeCells_localLength, asciiCheck_localLength,
    subAutomaton_localLength, mainAutomaton_localLength, Mul.circuit_localLength,
    matcher_localLength, matcher_output, oneHot_localLength, oneHot_output,
    routeSlot_localLength, routeSlot_output, lessThan_localLength, lessThan_output,
    ByteClass.sub_output_main, Emit.sub_output_main, CodePoint.sub_output_main,
    KeyIndex.sub_output_main, KeyMatchers.sub_output_main, ValueEmit.sub_output_main,
    Offset.sub_output_main, ClaimSignals.sub_output_main,
    ByteClass.main, ByteClass.mul, Emit.main, CodePoint.main, KeyIndex.main,
    KeyMatchers.main, Matcher.main, ValueEmit.main, Offset.main, ClaimSignals.main,
    Rows.freeze, Rows.mul]
  and_intros
  · exact CW.flat_subcircuit ByteClass.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) ByteClass.computableWitnesses env env'
  · exact CW.flat_assertion ClaimKinds.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) ClaimKinds.computableWitnesses env env'
  · exact CW.flat_subcircuit Mul.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) Mul.computableWitnesses env env'
  · exact CW.flat_assertion SubAutomaton.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) SubAutomaton.computableWitnesses env env'
  · exact CW.flat_assertion MainAutomaton.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) MainAutomaton.computableWitnesses env env'
  · exact CW.flat_subcircuit Emit.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) Emit.computableWitnesses env env'
  · exact CW.flat_general CodePoint.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) CodePoint.computableWitnesses env env'
  · exact CW.flat_general KeyIndex.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) KeyIndex.computableWitnesses env env'
  · exact CW.flat_general KeyMatchers.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) KeyMatchers.computableWitnesses env env'
  · exact CW.flat_assertion ClaimReg.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) ClaimReg.computableWitnesses env env'
  · exact CW.flat_subcircuit ValueEmit.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) ValueEmit.computableWitnesses env env'
  · exact CW.flat_general Offset.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) Offset.computableWitnesses env env'
  · exact CW.flat_general ClaimSignals.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) ClaimSignals.computableWitnesses env env'
  · -- the output block: project through the nested structs by the structural `eval`
    -- (normalising `eval env input` on the 664-cell output struct does not terminate)
    have hout : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input).out = ProvableStruct.eval e input.out := by
      intro e
      show Eval.eval e input.out = _
      rw [ProvableStruct.eval_eq_eval]
    have hslotiss : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).iss = ProvableStruct.eval e input.out.iss := by
      intro e
      show Eval.eval e input.out.iss = _
      rw [ProvableStruct.eval_eq_eval]
    have hveciss : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.iss).bytes
          = Vector.map (Expression.eval e) input.out.iss.bytes := by
      intro e
      show Eval.eval e input.out.iss.bytes = _
      simp only [circuit_norm]
    have houtiss : ∀ (m j : ℕ) (hj : j < 32),
        Stable m input (input.out.iss.bytes[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.iss.bytes[j]'hj) hp
      simpa only [hout, hslotiss, hveciss, Vector.getElem_map] using h
    have hslotsub : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).sub = ProvableStruct.eval e input.out.sub := by
      intro e
      show Eval.eval e input.out.sub = _
      rw [ProvableStruct.eval_eq_eval]
    have hvecsub : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.sub).bytes
          = Vector.map (Expression.eval e) input.out.sub.bytes := by
      intro e
      show Eval.eval e input.out.sub.bytes = _
      simp only [circuit_norm]
    have houtsub : ∀ (m j : ℕ) (hj : j < 32),
        Stable m input (input.out.sub.bytes[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.sub.bytes[j]'hj) hp
      simpa only [hout, hslotsub, hvecsub, Vector.getElem_map] using h
    have hslotaud : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).aud = ProvableStruct.eval e input.out.aud := by
      intro e
      show Eval.eval e input.out.aud = _
      rw [ProvableStruct.eval_eq_eval]
    have hvecaud : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.aud).bytes
          = Vector.map (Expression.eval e) input.out.aud.bytes := by
      intro e
      show Eval.eval e input.out.aud.bytes = _
      simp only [circuit_norm]
    have houtaud : ∀ (m j : ℕ) (hj : j < 128),
        Stable m input (input.out.aud.bytes[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.aud.bytes[j]'hj) hp
      simpa only [hout, hslotaud, hvecaud, Vector.getElem_map] using h
    have hslotazp : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).azp = ProvableStruct.eval e input.out.azp := by
      intro e
      show Eval.eval e input.out.azp = _
      rw [ProvableStruct.eval_eq_eval]
    have hvecazp : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.azp).bytes
          = Vector.map (Expression.eval e) input.out.azp.bytes := by
      intro e
      show Eval.eval e input.out.azp.bytes = _
      simp only [circuit_norm]
    have houtazp : ∀ (m j : ℕ) (hj : j < 128),
        Stable m input (input.out.azp.bytes[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.azp.bytes[j]'hj) hp
      simpa only [hout, hslotazp, hvecazp, Vector.getElem_map] using h
    have hslothd : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).hd = ProvableStruct.eval e input.out.hd := by
      intro e
      show Eval.eval e input.out.hd = _
      rw [ProvableStruct.eval_eq_eval]
    have hvechd : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.hd).bytes
          = Vector.map (Expression.eval e) input.out.hd.bytes := by
      intro e
      show Eval.eval e input.out.hd.bytes = _
      simp only [circuit_norm]
    have houthd : ∀ (m j : ℕ) (hj : j < 64),
        Stable m input (input.out.hd.bytes[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.hd.bytes[j]'hj) hp
      simpa only [hout, hslothd, hvechd, Vector.getElem_map] using h
    have hslotemail : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).email = ProvableStruct.eval e input.out.email := by
      intro e
      show Eval.eval e input.out.email = _
      rw [ProvableStruct.eval_eq_eval]
    have hvecemail : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.email).bytes
          = Vector.map (Expression.eval e) input.out.email.bytes := by
      intro e
      show Eval.eval e input.out.email.bytes = _
      simp only [circuit_norm]
    have houtemail : ∀ (m j : ℕ) (hj : j < 128),
        Stable m input (input.out.email.bytes[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.email.bytes[j]'hj) hp
      simpa only [hout, hslotemail, hvecemail, Vector.getElem_map] using h
    have hslotnonce : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).nonce = ProvableStruct.eval e input.out.nonce := by
      intro e
      show Eval.eval e input.out.nonce = _
      rw [ProvableStruct.eval_eq_eval]
    have hvecnonce : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.nonce).bytes
          = Vector.map (Expression.eval e) input.out.nonce.bytes := by
      intro e
      show Eval.eval e input.out.nonce.bytes = _
      simp only [circuit_norm]
    have houtnonce : ∀ (m j : ℕ) (hj : j < 64),
        Stable m input (input.out.nonce.bytes[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.nonce.bytes[j]'hj) hp
      simpa only [hout, hslotnonce, hvecnonce, Vector.getElem_map] using h
    have hslotatHash : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).atHash = ProvableStruct.eval e input.out.atHash := by
      intro e
      show Eval.eval e input.out.atHash = _
      rw [ProvableStruct.eval_eq_eval]
    have hvecatHash : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.atHash).bytes
          = Vector.map (Expression.eval e) input.out.atHash.bytes := by
      intro e
      show Eval.eval e input.out.atHash.bytes = _
      simp only [circuit_norm]
    have houtatHash : ∀ (m j : ℕ) (hj : j < 64),
        Stable m input (input.out.atHash.bytes[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.atHash.bytes[j]'hj) hp
      simpa only [hout, hslotatHash, hvecatHash, Vector.getElem_map] using h
    have hslotiat : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).iat = ProvableStruct.eval e input.out.iat := by
      intro e
      show Eval.eval e input.out.iat = _
      rw [ProvableStruct.eval_eq_eval]
    have hveciat : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.iat).digits
          = Vector.map (Expression.eval e) input.out.iat.digits := by
      intro e
      show Eval.eval e input.out.iat.digits = _
      simp only [circuit_norm]
    have houtiat : ∀ (m j : ℕ) (hj : j < 12),
        Stable m input (input.out.iat.digits[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.iat.digits[j]'hj) hp
      simpa only [hout, hslotiat, hveciat, Vector.getElem_map] using h
    have hslotexp : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out).exp = ProvableStruct.eval e input.out.exp := by
      intro e
      show Eval.eval e input.out.exp = _
      rw [ProvableStruct.eval_eq_eval]
    have hvecexp : ∀ (e : Environment (F circomPrime)),
        (ProvableStruct.eval e input.out.exp).digits
          = Vector.map (Expression.eval e) input.out.exp.digits := by
      intro e
      show Eval.eval e input.out.exp.digits = _
      simp only [circuit_norm]
    have houtexp : ∀ (m j : ℕ) (hj : j < 12),
        Stable m input (input.out.exp.digits[j]'hj) := by
      intro m j hj envA envB _ hp
      rw [CircuitType.eval_expression_prover_to_verifier,
        CircuitType.eval_expression_prover_to_verifier,
        ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval] at hp
      have h := congrArg (fun z : Inputs (F circomPrime) => z.out.exp.digits[j]'hj) hp
      simpa only [hout, hslotexp, hvecexp, Vector.getElem_map] using h
    exact CW.flat_assertion RouteCells.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) RouteCells.computableWitnesses env env'
  · exact CW.flat_assertion AsciiCheck.circuit input _ _ _ (by first | rfl | omega)
      (by stableP_tac) AsciiCheck.computableWitnesses env env'

end Step

end Solution.JSONExtract
