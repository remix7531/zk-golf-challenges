import Clean.Circuit

/-!
# Channel-lawfulness (the `requirementsChannelsLawful` obligation)

(A solution-side copy of the toolkit that used to live under `Challenge/Utils`: the
other baselines close the obligation with the field's default tactic, but `Step` is
too large for it -- normalizing its unfolded `main` never terminates.)

A Clean `FormalCircuitBase` carries channel metadata: `channelsWithRequirements`
lists the channels on which the circuit (or a subcircuit it calls) may add
*requirements*, and the field `requirementsChannelsLawful` proves that this list,
together with the `ElaboratedCircuit`'s `channelsWithGuarantees`, covers every
channel interaction the circuit performs:

```lean
requirementsChannelsLawful : ∀ input offset,
  ((main input).operations offset).RequirementsChannelsLawful
    elaborated.channelsWithGuarantees channelsWithRequirements
```

The challenge instances state this obligation with `channelsWithRequirements := []`
(a challenge circuit adds requirements on no channel), so a solution's `main` is a
genuine `GeneralFormalCircuit` whose end-to-end channel accounting is closed.

## The property

For an R1CS circuit the obligation is trivially true: an R1CS circuit performs
**no** channel interaction at all (`Challenge.CostR1CS.isR1CS` rejects every
`.interact` operation), so *any* pair of channel lists covers it. This file makes
that triviality mechanical:

- `NoChannelsCirc c` is a purely structural, environment-free certificate that
  `c` performs no shallow interaction and calls only subcircuits that declare no
  requirement channels, at every offset.
- `requirementsChannelsLawful_of_noChannels` turns that certificate into the
  `RequirementsChannelsLawful` obligation for **arbitrary** channel lists, so the
  `elaborated.channelsWithGuarantees` term never has to be reduced.

## Proving it

Mirror the `UsesIRCirc` proof in a solution's `Main.lean`: walk `main`'s `do`-block
with `NoChannelsCirc.bind` / `.forEach` / `.mapFinRange` / `.foldlRange`, discharge
every witness/assert/lookup with the matching leaf lemma, and every subcircuit
invocation with `NoChannelsCirc.subcircuit rfl` (resp. `.subcircuitWithAssertion`,
`.assertion`): the `rfl` checks that the child gadget's bundle declares
`channelsWithRequirements = []`, which is the `FormalCircuitBase` default. A child
gadget is never unfolded.

Note that, unlike `isR1CS`, the obligation quantifies over *every* symbolic input
(not only affine ones), so it cannot be derived from the R1CS certificate of `main`;
but the walk above needs no hypothesis on the input, so it is the same bind-chain
as `witgenIsIR`.
-/

namespace Solution.JSONExtract.ChannelsLawful

variable {F : Type} [FiniteField F] {α β : Type}

/-! ## The structural predicate -/

/-- No channel interaction in a (nested) operation list: no shallow `.interact`,
and every subcircuit declares no requirement channel. -/
def operationsNoChannels : Operations F → Prop
  | [] => True
  | .interact _ :: _ => False
  | .witness _ _ :: ops | .assert _ :: ops | .lookup _ :: ops => operationsNoChannels ops
  | .subcircuit s :: ops => s.channelsWithRequirements = [] ∧ operationsNoChannels ops

/-- A circuit performs no channel interaction, at every offset. -/
def NoChannelsCirc (c : Circuit F α) : Prop :=
  ∀ n, operationsNoChannels (c.operations n)

/-! ## Traversal lemmas -/

@[simp] theorem operationsNoChannels_nil :
    operationsNoChannels ([] : Operations F) = True := rfl

theorem operationsNoChannels_append (ops₁ ops₂ : Operations F) :
    operationsNoChannels (ops₁ ++ ops₂) ↔
      operationsNoChannels ops₁ ∧ operationsNoChannels ops₂ := by
  induction ops₁ with
  | nil => simp [operationsNoChannels]
  | cons op ops ih => cases op <;> simp [operationsNoChannels, ih, and_assoc]

theorem operationsNoChannels_flatten_ofFn {m : ℕ} (g : Fin m → Operations F)
    (h : ∀ i, operationsNoChannels (g i)) :
    operationsNoChannels (List.ofFn g).flatten := by
  induction m with
  | zero => simp [List.ofFn_zero, List.flatten_nil]
  | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons, operationsNoChannels_append]
      exact ⟨h 0, ih (fun i => g i.succ) (fun i => h i.succ)⟩

/-! ## The bridge to Clean's obligation -/

theorem shallowInteractions_eq_nil_of_noChannels {ops : Operations F}
    (h : operationsNoChannels ops) : ops.shallowInteractions = [] := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
      cases op with
      | interact i => exact absurd h id
      | subcircuit s => exact ih h.2
      | witness m c => exact ih h
      | assert e => exact ih h
      | lookup l => exact ih h

theorem subcircuitChannelsWithRequirements_eq_nil_of_noChannels {ops : Operations F}
    (h : operationsNoChannels ops) : ops.subcircuitChannelsWithRequirements = [] := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
      cases op with
      | interact i => exact absurd h id
      | subcircuit s =>
          rw [Operations.subcircuitChannelsWithRequirements_subcircuit, h.1, ih h.2]; rfl
      | witness m c => exact ih h
      | assert e => exact ih h
      | lookup l => exact ih h

theorem shallowChannels_eq_nil_of_noChannels {ops : Operations F}
    (h : operationsNoChannels ops) : ops.shallowChannels = [] := by
  rw [Operations.shallowChannels_eq_interactions_map, shallowInteractions_eq_nil_of_noChannels h]
  rfl

/-- A channel-free operation list satisfies `RequirementsChannelsLawful` for *any*
guarantee and requirement channel lists. -/
theorem requirementsChannelsLawful_of_noChannels {ops : Operations F}
    (h : operationsNoChannels ops)
    (channelsWithGuarantees channelsWithRequirements : List (RawChannel F)) :
    ops.RequirementsChannelsLawful channelsWithGuarantees channelsWithRequirements := by
  refine ⟨?_, ?_, ?_⟩
  · rw [subcircuitChannelsWithRequirements_eq_nil_of_noChannels h]
    exact List.nil_subset _
  · intro channel hc
    rw [shallowChannels_eq_nil_of_noChannels h] at hc
    exact absurd hc List.not_mem_nil
  · intro env _
    rw [Operations.inChannelsOrRequirements_iff_forall_mem,
      shallowInteractions_eq_nil_of_noChannels h]
    intro i hi
    exact absurd hi List.not_mem_nil

/-- A channel-free operation list has no shallow requirement to discharge: the
`Operations.Requirements` conjunct of `GeneralFormalCircuit.Soundness`. -/
theorem requirements_of_noChannels {env : Environment F} {ops : Operations F}
    (h : operationsNoChannels ops) : Operations.Requirements env ops := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
      cases op with
      | interact i => exact absurd h id
      | subcircuit s => exact ⟨Or.inl h.1, ih h.2⟩
      | witness m c => exact ⟨trivial, ih h⟩
      | assert e => exact ⟨trivial, ih h⟩
      | lookup l => exact ⟨trivial, ih h⟩

/-- The shape in which a challenge instance states the obligation: `main`'s
operations are channel-lawful for the elaborated guarantee channels and no
requirement channel, at every input and offset. -/
theorem requirementsChannelsLawful_of_noChannelsCirc {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {main : Var Input F → Circuit F (Var Output F)}
    (elaborated : ElaboratedCircuit F Input Output main)
    (h : ∀ input, NoChannelsCirc (main input)) :
    ∀ input offset, ((main input).operations offset).RequirementsChannelsLawful
      elaborated.channelsWithGuarantees [] :=
  fun input offset => requirementsChannelsLawful_of_noChannels (h input offset) _ _

/-! ## Structural lemmas: monadic skeleton -/

theorem NoChannelsCirc.pure (a : α) : NoChannelsCirc (pure a : Circuit F α) := by
  intro n; rw [Circuit.pure_operations_eq]; trivial

theorem NoChannelsCirc.bind {f : Circuit F α} {g : α → Circuit F β}
    (hf : NoChannelsCirc f) (hg : ∀ a, NoChannelsCirc (g a)) : NoChannelsCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, operationsNoChannels_append]
  exact ⟨hf n, hg _ _⟩

theorem NoChannelsCirc.map {f : Circuit F α} {g : α → β} (hf : NoChannelsCirc f) :
    NoChannelsCirc (g <$> f) := by
  intro n; rw [Circuit.map_operations_eq]; exact hf n

/-! ## Structural lemmas: witness entry points (all accepted) -/

theorem NoChannelsCirc.witnessVar (ir : Witgen.WitgenIR F 1) :
    NoChannelsCirc (Circuit.witnessVar ir) := by
  intro n; trivial

theorem NoChannelsCirc.witnessField (e : Witgen.FExpr F) :
    NoChannelsCirc (Circuit.witnessField e) := by
  intro n; trivial

theorem NoChannelsCirc.witnessVector (m : ℕ) (out : Witgen.VExpr F m) :
    NoChannelsCirc (Circuit.witnessVector m out) := by
  intro n; trivial

theorem NoChannelsCirc.witnessVectorNative (m : ℕ) (c : ProverEnvironment F → Vector F m) :
    NoChannelsCirc (witnessVectorNative m c) := by
  intro n; trivial

theorem NoChannelsCirc.witnessIR (M : TypeMap) [ProvableType M]
    (ir : Witgen.WitgenIR F (size M)) : NoChannelsCirc (_root_.witnessIR M ir) := by
  intro n; trivial

theorem NoChannelsCirc.witnessNative {M : TypeMap} [ProvableType M]
    (c : ProverEnvironment F → M F) :
    NoChannelsCirc (witnessNative (var := Var M) c) := by
  intro n; trivial

theorem NoChannelsCirc.witnessFieldNative (c : ProverEnvironment F → F) :
    NoChannelsCirc (_root_.witnessNative (value := field) (var := Expression) c) := by
  intro n; trivial

theorem NoChannelsCirc.witnessVectorProgram (m : ℕ) (program : Witgen.M F (Witgen.VExpr F m)) :
    NoChannelsCirc (witnessVectorProgram m program) := by
  intro n; trivial

theorem NoChannelsCirc.witnessProgram {M : TypeMap} [ProvableType M]
    (program : Witgen.M F (M (Witgen.FExpr F))) :
    NoChannelsCirc (witnessProgram (value := M) (var := Var M) program) := by
  intro n; trivial

theorem NoChannelsCirc.witnessValue {M : TypeMap} [ProvableType M]
    (xs : M (Witgen.FExpr F)) :
    NoChannelsCirc (witness (F := F) (value := M) (var := Var M) xs) := by
  intro n; trivial

theorem NoChannelsCirc.witnessFieldValue (e : Witgen.FExpr F) :
    NoChannelsCirc (witness (F := F) (value := field) (var := Expression) e) := by
  intro n; trivial

theorem NoChannelsCirc.witnessVectorValue {m : ℕ} (xs : fields m (Witgen.FExpr F)) :
    NoChannelsCirc (witness (F := F) (value := fields m) (var := Var (fields m)) xs) := by
  intro n; trivial

/-! ## Structural lemmas: non-witness operations -/

theorem NoChannelsCirc.assertZero (e : Expression F) :
    NoChannelsCirc (Circuit.assertZero e) := by
  intro n; trivial

theorem NoChannelsCirc.lookup {Row : TypeMap} [ProvableType Row] (table : Table F Row)
    (entry : Row (Expression F)) : NoChannelsCirc (Circuit.lookup table entry) := by
  intro n; trivial

/-! ## Structural lemmas: subcircuits

A subcircuit invocation is channel-free exactly when the invoked bundle declares no
requirement channel (`channelsWithRequirements = []`, the `FormalCircuitBase`
default, so `rfl` discharges the hypothesis for every gadget built without
channels). -/

/-- Invoking a `FormalCircuit` as a subcircuit. -/
theorem NoChannelsCirc.subcircuit {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : FormalCircuit F Input Output} {b : Var Input F}
    (h : circuit.channelsWithRequirements = []) :
    NoChannelsCirc (_root_.subcircuit circuit b) := by
  intro n
  show operationsNoChannels [Operation.subcircuit (circuit.toSubcircuit n b)]
  exact ⟨h, trivial⟩

/-- Same as `NoChannelsCirc.subcircuit`, for a `GeneralFormalCircuit`. -/
theorem NoChannelsCirc.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit F Input Output} {b : Var Input F}
    (h : circuit.channelsWithRequirements = []) :
    NoChannelsCirc (subcircuitWithAssertion circuit b) := by
  intro n
  show operationsNoChannels [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  rw [GeneralFormalCircuit.toSubcircuit_channelsWithRequirements]
  exact h

/-- Same as `NoChannelsCirc.subcircuit`, for a `FormalAssertion`. -/
theorem NoChannelsCirc.assertion {Input : TypeMap} [ProvableType Input]
    {circuit : FormalAssertion F Input} {b : Var Input F}
    (h : circuit.channelsWithRequirements = []) :
    NoChannelsCirc (_root_.assertion circuit b) := by
  intro n
  show operationsNoChannels [Operation.subcircuit (circuit.toSubcircuit n b)]
  exact ⟨h, trivial⟩

/-! ## Structural lemmas: loops -/

theorem NoChannelsCirc.forEach {m : ℕ} [Inhabited α] {xs : Vector α m} {body : α → Circuit F Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ a n, operationsNoChannels ((body a).operations n)) :
    NoChannelsCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsNoChannels_flatten_ofFn _ (fun i => h _ _)

theorem NoChannelsCirc.mapFinRange {m : ℕ} [NeZero m] {body : Fin m → Circuit F β}
    {constant : Circuit.ConstantLength body}
    (h : ∀ i n, operationsNoChannels ((body i).operations n)) :
    NoChannelsCirc (Circuit.mapFinRange m body constant) := by
  intro n
  rw [Circuit.mapFinRange.operations_eq]
  exact operationsNoChannels_flatten_ofFn _ (fun i => h _ _)

theorem NoChannelsCirc.foldlRange {m : ℕ} [Inhabited β] {init : β} {body : β → Fin m → Circuit F β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2}
    (h : ∀ s i n, operationsNoChannels ((body s i).operations n)) :
    NoChannelsCirc (Circuit.foldlRange m init body constant) := by
  intro n
  rw [Circuit.foldlRange.operations_eq]
  exact operationsNoChannels_flatten_ofFn _ (fun i => h _ _ _)

/-! ## Loop lemmas in `NoChannelsCirc` shape

The hypotheses above are stated in the unfolded `∀ a n, operationsNoChannels ...`
form, which a structural walk cannot match syntactically; these restate them so the
body obligation is again a `NoChannelsCirc` goal. -/

theorem NoChannelsCirc.forEach' {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit F Unit} {constant : Circuit.ConstantLength body}
    (h : ∀ a, NoChannelsCirc (body a)) :
    NoChannelsCirc (Circuit.forEach xs body constant) :=
  NoChannelsCirc.forEach fun a n => h a n

theorem NoChannelsCirc.mapFinRange' {m : ℕ} [NeZero m] {body : Fin m → Circuit F β}
    {constant : Circuit.ConstantLength body}
    (h : ∀ i, NoChannelsCirc (body i)) :
    NoChannelsCirc (Circuit.mapFinRange m body constant) :=
  NoChannelsCirc.mapFinRange fun i n => h i n

theorem NoChannelsCirc.foldlRange' {m : ℕ} [Inhabited β] {init : β}
    {body : β → Fin m → Circuit F β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2}
    (h : ∀ s i, NoChannelsCirc (body s i)) :
    NoChannelsCirc (Circuit.foldlRange m init body constant) :=
  NoChannelsCirc.foldlRange fun s i n => h s i n

/-! ## Teeth: an interaction is refuted -/

theorem not_noChannelsCirc_interact (i : AbstractInteraction F) :
    ¬ NoChannelsCirc (fun _offset => ((), [.interact i]) : Circuit F Unit) := by
  intro h
  exact h 0

end Solution.JSONExtract.ChannelsLawful
