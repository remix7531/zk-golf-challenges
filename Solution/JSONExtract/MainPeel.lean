import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.MainTheorems

/-!
# Peeling the top-level circuit (`JSONExtract`)

`Main.soundness` / `Main.completeness` cannot use `circuit_proof_start`: `main`
is a 26-block `do` spine whose fourteenth block is a 1024-iteration
`Circuit.map` of a 1269-witness gadget, and normalising the operation list with
`circuit_norm` unfolds the loop.  The lemmas here peel one block at a time,
keyed on the `do`-former rather than on the operation list, and leave the
successor offset and the block's output as *opaque locals*, so no hypothesis
ever mentions the accumulated offset arithmetic.

Everything in this file is generic in the circuit; nothing mentions `main`.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

namespace MainPeel

variable {K : Type} [FiniteField K] {α β γ : Type}

/-! ## Soundness -/

/-- Split one bind of a soundness hypothesis, generalizing the successor offset
and the bound value to fresh locals.  The bound value comes with its defining
equation, which the `Circuit.map` block needs (to identify the per-position
signal vector with the loop bodies' outputs) and every other block discards. -/
theorem chs_bind (env : Environment K) {f : Circuit K α} {g : α → Circuit K β} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((f >>= g).operations n)) :
    ∃ (m : ℕ) (x : α), x = f.output n ∧ (f >>= g).output n = (g x).output m ∧
      ConstraintsHold.Soundness env (f.operations n) ∧
      ConstraintsHold.Soundness env ((g x).operations m) :=
  ⟨_, _, rfl, rfl, (Circuit.bind_forAllNoOffset.mp h).1,
    (Circuit.bind_forAllNoOffset.mp h).2⟩

/-- A `Circuit.map` block, soundness side. -/
theorem chs_map {m n : ℕ} [Inhabited α] {xs : Vector α m} {body : α → Circuit K β}
    {constant : Circuit.ConstantLength body} {env : Environment K} :
    ConstraintsHold.Soundness env ((Circuit.map xs body constant).operations n) ↔
      ∀ i : Fin m, ConstraintsHold.Soundness env
        ((body xs[i.val]).operations (n + i * (body default).localLength)) :=
  Circuit.map.forAllNoOffset

/-- A `FormalAssertion` block, soundness side. -/
theorem chs_assertion {Inp : TypeMap} [ProvableType Inp] {env : Environment K}
    {circuit : FormalAssertion K Inp} {b : Var Inp K} {n : ℕ} :
    ConstraintsHold.Soundness env ((assertion circuit b).operations n) ↔
      (circuit.Assumptions (eval env b) → circuit.Spec (eval env b)) := by
  simp [circuit_norm]

/-- A `GeneralFormalCircuit` block, soundness side. -/
theorem chs_subA {Inp Out : TypeMap} [ProvableType Inp] [ProvableType Out] {env : Environment K}
    {circuit : GeneralFormalCircuit K Inp Out} {b : Var Inp K} {n : ℕ} :
    ConstraintsHold.Soundness env ((subcircuitWithAssertion circuit b).operations n) ↔
      (circuit.Assumptions (eval env b) env.data →
        circuit.Spec (eval env b) (eval env (circuit.output b n)) env.data) := by
  simp [circuit_norm]


/-- A `Circuit.map` of a `GeneralFormalCircuit`, soundness side, with the loop's
offset arithmetic hidden: the `i`-th body sees the `i`-th input and returns the
`i`-th entry of the loop's output vector. -/
theorem chs_map_subA {Inp Out : TypeMap} [ProvableType Inp] [ProvableType Out]
    {m n : ℕ} [Inhabited α] {xs : Vector α m}
    {circuit : GeneralFormalCircuit K Inp Out} {g : α → Var Inp K}
    {constant : Circuit.ConstantLength (fun a => subcircuitWithAssertion circuit (g a))}
    {env : Environment K}
    (h : ConstraintsHold.Soundness env
      ((Circuit.map xs (fun a => subcircuitWithAssertion circuit (g a)) constant).operations n)) :
    ∀ i : Fin m,
      circuit.Assumptions (eval env (g xs[i.val])) env.data →
        circuit.Spec (eval env (g xs[i.val]))
          (eval env ((Circuit.map xs (fun a => subcircuitWithAssertion circuit (g a))
            constant).output n)[i.val]) env.data := by
  intro i hA
  have h1 := chs_subA.mp (Circuit.map.forAllNoOffset.mp h i)
  have h2 : ((Circuit.map xs (fun a => subcircuitWithAssertion circuit (g a))
        constant).output n)[i.val]
      = circuit.output (g xs[i.val])
        (n + i.val * ((fun a => subcircuitWithAssertion circuit (g a)) default).localLength) := by
    rw [Circuit.map.output_eq]
    simp only [Vector.getElem_mapIdx]
    rfl
  rw [h2]
  exact h1 hA

/-! ## Requirements

`Operations.Requirements` is *shallow*: its `subcircuit` clause only asks that
the child declares no requirement channels.  Every gadget of `main` does, so
the whole obligation peels away in one descent. -/

theorem req_bind (env : Environment K) {f : Circuit K α} {g : α → Circuit K β} {n : ℕ}
    (h1 : Operations.Requirements env (f.operations n))
    (h2 : ∀ (m : ℕ) (x : α), Operations.Requirements env ((g x).operations m)) :
    Operations.Requirements env ((f >>= g).operations n) :=
  Circuit.bind_forAllNoOffset.mpr ⟨h1, h2 _ _⟩

theorem req_witnessIR (env : Environment K) (M : TypeMap) [ProvableType M]
    (ir : Witgen.WitgenIR K (size M)) (n : ℕ) :
    Operations.Requirements env ((witnessIR M ir).operations n) := ⟨trivial, trivial⟩

theorem req_witnessVector (env : Environment K) (m : ℕ) (out : Witgen.VExpr K m) (n : ℕ) :
    Operations.Requirements env ((Circuit.witnessVector m out).operations n) := ⟨trivial, trivial⟩

theorem req_assertion {Inp : TypeMap} [ProvableType Inp] (env : Environment K)
    (circuit : FormalAssertion K Inp) (hc : circuit.channelsWithRequirements = [])
    (b : Var Inp K) (n : ℕ) :
    Operations.Requirements env ((assertion circuit b).operations n) :=
  ⟨Or.inl ((FormalAssertion.toSubcircuit_channelsWithRequirements circuit).trans hc), trivial⟩

theorem req_subA {Inp Out : TypeMap} [ProvableType Inp] [ProvableType Out] (env : Environment K)
    (circuit : GeneralFormalCircuit K Inp Out) (hc : circuit.channelsWithRequirements = [])
    (b : Var Inp K) (n : ℕ) :
    Operations.Requirements env ((subcircuitWithAssertion circuit b).operations n) :=
  ⟨Or.inl ((GeneralFormalCircuit.toSubcircuit_channelsWithRequirements circuit).trans hc),
    trivial⟩

theorem req_pure (env : Environment K) (a : α) (n : ℕ) :
    Operations.Requirements env ((pure a : Circuit K α).operations n) := trivial

theorem req_map {m n : ℕ} [Inhabited α] {xs : Vector α m} {body : α → Circuit K β}
    {constant : Circuit.ConstantLength body} {env : Environment K}
    (h : ∀ (j : ℕ) (x : α), Operations.Requirements env ((body x).operations j)) :
    Operations.Requirements env ((Circuit.map xs body constant).operations n) :=
  Circuit.map.forAllNoOffset.mpr fun _ => h _ _

/-! ## Completeness

The completeness side is a *construction*, so the peel goes the other way: each
lemma consumes the `UsesLocalWitnessesCompleteness` hypothesis of one block,
hands its continuation the freshly bound variable together with the fact that it
evaluates to the block's witness generator, and asks for the constraints of the
tail. -/

/-- The witnessed value of a `witnessIR` block, elementwise. -/
theorem eval_varFromOffset_of_extends {M : TypeMap} [ProvableType M]
    (env : ProverEnvironment K) (w : Vector K (size M)) (n : ℕ)
    (h : env.ExtendsVector w n) :
    ∀ (i : ℕ) (hi : i < size M),
      Expression.eval env.toEnvironment
        (ProvableType.toElements (varFromOffset M n : M (Expression K)))[i] = w[i] := by
  intro i hi
  rw [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]
  exact h ⟨i, hi⟩

/-- Peel a `witnessIR` row. -/
theorem chc_witnessIR_bind (M : TypeMap) [ProvableType M] (env : ProverEnvironment K)
    (ir : Witgen.WitgenIR K (size M)) (g : M (Expression K) → Circuit K β) (n : ℕ)
    (h_env : env.UsesLocalWitnessesCompleteness n ((witnessIR M ir >>= g).operations n))
    (ih : ∀ (v : M (Expression K)) (n' : ℕ),
        (∀ (i : ℕ) (hi : i < size M),
          Expression.eval env.toEnvironment (ProvableType.toElements v)[i] = (ir.eval env)[i]) →
        env.UsesLocalWitnessesCompleteness n' ((g v).operations n') →
        ConstraintsHold.Completeness env ((g v).operations n')) :
    ConstraintsHold.Completeness env ((witnessIR M ir >>= g).operations n) := by
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
  refine Circuit.bind_forAllNoOffset.mpr ⟨⟨trivial, trivial⟩, ?_⟩
  exact ih _ _ (eval_varFromOffset_of_extends env _ n h_env.1.1) h_env.2

/-- Peel a `witnessVector` row. -/
theorem chc_witnessVector_bind {m : ℕ} (env : ProverEnvironment K)
    (out : Witgen.VExpr K m) (g : Vector (Expression K) m → Circuit K β) (n : ℕ)
    (h_env : env.UsesLocalWitnessesCompleteness n ((Circuit.witnessVector m out >>= g).operations n))
    (ih : ∀ (v : Vector (Expression K) m) (n' : ℕ),
        (∀ (i : ℕ) (hi : i < m),
          Expression.eval env.toEnvironment v[i] = (out.eval { env := env, locals := #[] })[i]) →
        env.UsesLocalWitnessesCompleteness n' ((g v).operations n') →
        ConstraintsHold.Completeness env ((g v).operations n')) :
    ConstraintsHold.Completeness env ((Circuit.witnessVector m out >>= g).operations n) := by
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
  refine Circuit.bind_forAllNoOffset.mpr ⟨⟨trivial, trivial⟩, ?_⟩
  refine ih _ _ (fun i hi => ?_) h_env.2
  show Expression.eval env.toEnvironment (varFromOffset (fields m) n)[i] = _
  rw [ProvableType.varFromOffset_fields, Vector.getElem_mapRange]
  exact h_env.1.1 ⟨i, hi⟩

/-- A `FormalAssertion` block, completeness side. -/
theorem chc_assertion_iff {Inp : TypeMap} [ProvableType Inp] {env : ProverEnvironment K}
    {circuit : FormalAssertion K Inp} {b : Var Inp K} {n : ℕ} :
    ConstraintsHold.Completeness env ((assertion circuit b).operations n) ↔
      (circuit.Assumptions (eval env b) ∧ circuit.Spec (eval env b)) := by
  simp [circuit_norm]

/-- A `GeneralFormalCircuit` block, completeness side. -/
theorem chc_subA_iff {Inp Out : TypeMap} [ProvableType Inp] [ProvableType Out]
    {env : ProverEnvironment K} {circuit : GeneralFormalCircuit K Inp Out} {b : Var Inp K}
    {n : ℕ} :
    ConstraintsHold.Completeness env ((subcircuitWithAssertion circuit b).operations n) ↔
      circuit.ProverAssumptions (eval env b) env.data env.hint := by
  simp [circuit_norm]

/-- Peel a `FormalAssertion` block. -/
theorem chc_assertion_bind {Inp : TypeMap} [ProvableType Inp] (env : ProverEnvironment K)
    (circuit : FormalAssertion K Inp) (b : Var Inp K) (g : Unit → Circuit K β) (n : ℕ)
    (h_env : env.UsesLocalWitnessesCompleteness n ((assertion circuit b >>= g).operations n))
    (h1 : circuit.Assumptions (eval env b))
    (h2 : circuit.Spec (eval env b))
    (ih : ∀ (n' : ℕ), env.UsesLocalWitnessesCompleteness n' ((g ()).operations n') →
        ConstraintsHold.Completeness env ((g ()).operations n')) :
    ConstraintsHold.Completeness env ((assertion circuit b >>= g).operations n) := by
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
  exact Circuit.bind_forAllNoOffset.mpr ⟨chc_assertion_iff.mpr ⟨h1, h2⟩, ih _ h_env.2⟩

/-- Peel a `GeneralFormalCircuit` block. -/
theorem chc_subA_bind {Inp Out : TypeMap} [ProvableType Inp] [ProvableType Out]
    (env : ProverEnvironment K) (circuit : GeneralFormalCircuit K Inp Out) (b : Var Inp K)
    (g : Var Out K → Circuit K β) (n : ℕ)
    (h_env : env.UsesLocalWitnessesCompleteness n
      ((subcircuitWithAssertion circuit b >>= g).operations n))
    (h1 : circuit.ProverAssumptions (eval env b) env.data env.hint)
    (ih : ∀ (v : Var Out K) (n' : ℕ), v = circuit.output b n →
        env.UsesLocalWitnessesCompleteness n' ((g v).operations n') →
        ConstraintsHold.Completeness env ((g v).operations n')) :
    ConstraintsHold.Completeness env ((subcircuitWithAssertion circuit b >>= g).operations n) := by
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
  exact Circuit.bind_forAllNoOffset.mpr ⟨chc_subA_iff.mpr h1, ih _ _ rfl h_env.2⟩

/-- Peel the `Circuit.map` block: only the per-position constraints are needed,
the loop's own witnesses live inside the subcircuits. -/
theorem chc_map_bind {m : ℕ} [Inhabited α] (env : ProverEnvironment K) {xs : Vector α m}
    {body : α → Circuit K β} {constant : Circuit.ConstantLength body}
    {g : Vector β m → Circuit K γ} {n : ℕ}
    (h_env : env.UsesLocalWitnessesCompleteness n
      ((Circuit.map xs body constant >>= g).operations n))
    (h1 : ∀ (i : Fin m) (j : ℕ), ConstraintsHold.Completeness env ((body xs[i.val]).operations j))
    (ih : ∀ (v : Vector β m) (n' : ℕ), v = (Circuit.map xs body constant).output n →
        env.UsesLocalWitnessesCompleteness n ((Circuit.map xs body constant).operations n) →
        env.UsesLocalWitnessesCompleteness n' ((g v).operations n') →
        ConstraintsHold.Completeness env ((g v).operations n')) :
    ConstraintsHold.Completeness env ((Circuit.map xs body constant >>= g).operations n) := by
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
  refine Circuit.bind_forAllNoOffset.mpr ⟨Circuit.map.forAllNoOffset.mpr fun i => h1 i _, ?_⟩
  exact ih _ _ rfl h_env.1 h_env.2

/-- The per-position specification a `Circuit.map` of a `GeneralFormalCircuit`
hands the honest prover: the loop's own `UsesLocalWitnesses` obligation. -/
theorem ulwc_map_subA {Inp Out : TypeMap} [ProvableType Inp] [ProvableType Out]
    {m n : ℕ} [Inhabited α] {xs : Vector α m}
    {circuit : GeneralFormalCircuit K Inp Out} {g : α → Var Inp K}
    {constant : Circuit.ConstantLength (fun a => subcircuitWithAssertion circuit (g a))}
    {env : ProverEnvironment K}
    (h : env.UsesLocalWitnessesCompleteness n
      ((Circuit.map xs (fun a => subcircuitWithAssertion circuit (g a)) constant).operations n)) :
    ∀ i : Fin m, circuit.ProverAssumptions (eval env (g xs[i.val])) env.data env.hint →
      (circuit.Assumptions (eval env (g xs[i.val])) env.data →
        circuit.Spec (eval env (g xs[i.val]))
          (eval env ((Circuit.map xs (fun a => subcircuitWithAssertion circuit (g a))
            constant).output n)[i.val]) env.data) := by
  intro i hPA hA
  have h1 := Circuit.map.usesLocalWitnesses.mp h i
  rw [Step.wsubA] at h1
  have h2 : ((Circuit.map xs (fun a => subcircuitWithAssertion circuit (g a))
        constant).output n)[i.val]
      = circuit.output (g xs[i.val])
        (n + i.val * ((fun a => subcircuitWithAssertion circuit (g a)) default).localLength) := by
    rw [Circuit.map.output_eq]
    simp only [Vector.getElem_mapIdx]
    rfl
  rw [h2]
  exact (h1 hPA).1 hA

/-- The last block of the spine. -/
theorem chc_pure (env : ProverEnvironment K) (a : α) (n : ℕ) :
    ConstraintsHold.Completeness env ((pure a : Circuit K α).operations n) := trivial

end MainPeel
end Solution.JSONExtract
