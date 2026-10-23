import Challenge.Utils.CostR1CS
import Challenge.Utils.WitgenIR
import Challenge.Instances.JSONExtract.Interface
import Clean.Utils.Bits
import Clean.Circomlib.Bitify
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Mul
import Solution.JSONExtract.LenFlags
import Solution.JSONExtract.OneHot
import Solution.JSONExtract.FilledMask
import Solution.JSONExtract.ByteClass
import Solution.JSONExtract.SubAutomaton
import Solution.JSONExtract.MainAutomaton
import Solution.JSONExtract.Matcher
import Solution.JSONExtract.RouteSlot
import Solution.JSONExtract.Rows
import Solution.JSONExtract.ClaimKinds
import Solution.JSONExtract.Emit
import Solution.JSONExtract.CodePoint
import Solution.JSONExtract.KeyIndex
import Solution.JSONExtract.KeyMatchers
import Solution.JSONExtract.ClaimReg
import Solution.JSONExtract.ValueEmit
import Solution.JSONExtract.Offset
import Solution.JSONExtract.ClaimSignals
import Solution.JSONExtract.RouteHalf
import Solution.JSONExtract.RouteCells
import Solution.JSONExtract.AsciiCheck
import Solution.JSONExtract.Step
import Solution.JSONExtract.Anchors
import Solution.JSONExtract.Acceptance
import Solution.JSONExtract.SlotPins
import Solution.JSONExtract.MainTheorems

/-!
# Compositional cost, R1CS and witness-IR certificates (`JSONExtract`)

Bottom-up `operationCount` / `operationsIsR1CS` / `operationsUseIR` certificates for
every gadget of the extractor, proved with the compositional combinators of
`Challenge.Utils.CostR1CS` and `Challenge.Utils.WitgenIR`: no `native_decide`, no
large `decide`, and no reduction of a whole circuit. `Main.lean` assembles the three
top-level obligations (`mainCost`, `isR1CS`, `witgenIsIR`) from the certificates here.

The per-gadget counts (allocations, constraints):

| gadget | allocations | constraints |
|---|---|---|
| `Mul` | 1 | 1 |
| `Num2Bits n` | `n` | `n + 1` |
| `IsZero` / `IsEqual` | 2 | 2 |
| `LessThan n` | `n + 2` | `n + 3` |
| `LenFlags` | 0 | `flagLen + 2` |
| `OneHot n` | `n` | `n + 2` |
| `FilledMask n` | `n` | `3n + 1` |
| `ByteClass` | 108 | 109 |
| `SubAutomaton` | 49 | 76 |
| `MainAutomaton` | 99 | 154 |
| `Matcher k` | 8 | 9 |
| `RouteSlot n` | `n + 2` | `n + 2` |
| `Step` | 1269 | 1410 |
| `Anchors` | 0 | 29 |
| `Acceptance` | 33 | 37 |
| `StrSlotPin n` | `n` | `3n + 4` |
| `IntSlotPin n` | `n` | `3n + 5` |
| `BoolSlotPin` | 0 | 3 |
-/

namespace Solution.JSONExtract
namespace Cost

open Challenge.Instances.JSONExtract.Interface
open Challenge.CostR1CS
open Challenge.WitgenIR
open Circomlib
open Utils.Bits
open ProvableType (varFromOffset)

-- `maxRecDepth` controls elaboration stack depth only (not the trusted base and not the
-- heartbeat budget); the deep `do`-blocks of `ByteClass` and `Step` need more than the default.
set_option maxRecDepth 20000
set_option profiler true
set_option profiler.threshold 1000

/-- Two counts are equal when both components are. -/
theorem Count.ext' {K K' : Count} (ha : K.allocations = K'.allocations)
    (hc : K.constraints = K'.constraints) : K = K' := by
  cases K; cases K'; simp_all

/-! ## Generic bridges

`FormalCircuit` and `FormalAssertion` already have structural bridges in
`Challenge.CostR1CS` / `Challenge.WitgenIR`. Clean represents a circuit that has both
an output and an assertion-level specification as a `GeneralFormalCircuit`, whose
`subcircuitWithAssertion` wrapper has the same one-nested-operation shape; record that
once here rather than unfolding a formal bundle at every consumer. -/

theorem CostIs.subcircuitWithAssertion {F : Type} [FiniteField F]
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit F Input Output} {b : Var Input F} {K : Count}
    (h : ∀ n, operationCount ((circuit.main b).operations n) = K) :
    CostIs (subcircuitWithAssertion circuit b) K := by
  intro n
  show operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] = K
  have hz : operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] =
      nestedCount (circuit.toSubcircuit n b).ops := by
    show nestedCount _ + operationCount ([] : Operations F) = nestedCount _
    rw [show operationCount ([] : Operations F) = Count.zero from rfl, Count.add_zero]
  rw [hz]
  show nestedCount (NestedOperations.nested
    ⟨circuit.name, ((circuit.main b).operations n).toNested⟩) = K
  rw [show nestedCount (NestedOperations.nested
        ⟨circuit.name, ((circuit.main b).operations n).toNested⟩)
        = nestedListCount ((circuit.main b).operations n).toNested from rfl,
      Lemmas.operationCount_toNested]
  exact h n

theorem IsR1CSCirc.subcircuitWithAssertion {F : Type} [FiniteField F]
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit F Input Output} {b : Var Input F}
    (h : ∀ n, operationsIsR1CS ((circuit.main b).operations n)) :
    IsR1CSCirc (subcircuitWithAssertion circuit b) := by
  intro n
  show operationsIsR1CS [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsIsR1CS (circuit.toSubcircuit n b).ops.toFlat
  have hflat : (circuit.toSubcircuit n b).ops.toFlat =
      ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested
      ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hflat]
  exact (Lemmas.operationsIsR1CS_iff_toFlat _).mp (h n)

/-- Index-aware `forEach`: unlike the ordinary combinator, this may use facts about
the actual vector entry selected at an index (the booleanity rows need the entry). -/
theorem IsR1CSCirc.forEach_mem {F : Type} [FiniteField F] {α : Type} {m : ℕ}
    [Inhabited α] {xs : Vector α m} {body : α → Circuit F Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)

/-- Index-aware `Circuit.map` cost: `Circuit.map` is `mapFinRange` over the indices. -/
theorem CostIs.mapVec {F : Type} [FiniteField F] {α β : Type} {m : ℕ} [NeZero m]
    [Inhabited α] {xs : Vector α m} {body : α → Circuit F β}
    {constant : Circuit.ConstantLength body} {K : Count}
    (h : ∀ a n, operationCount ((body a).operations n) = K) :
    CostIs (Circuit.map xs body constant) ⟨m * K.allocations, m * K.constraints⟩ := by
  intro n
  rw [Circuit.map.operations_eq]
  exact operationCount_flatten_ofFn_const _ K (fun i => h _ _)

/-! ## Scalar equality and assignment

Clean's `===` on a field is the one-row `Gadgets.Equality` assertion; `<==` is a fresh
IR witness (`.expr rhs`) followed by that equality. -/

theorem costIs_assertEqualsM {M : TypeMap} [ProvableType M] (x y : Var M (F circomPrime)) :
    CostIs (assertEquals x y) ⟨0, size M⟩ := by
  refine CostIs.assertion (K := ⟨0, size M⟩) fun n => ?_
  show operationCount ((Gadgets.Equality.main (M := M) (x, y)).operations n) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := size M) (fun a k => CostIs.assertZero _ k) n)

theorem costIs_assertEquals (x y : Expression (F circomPrime)) :
    CostIs (Expression.assertEquals x y) ⟨0, 1⟩ :=
  costIs_assertEqualsM (M := field) x y

theorem r1cs_assertEqualsM {M : TypeMap} [ProvableType M] (x y : Var M (F circomPrime))
    (hrow : ∀ i : Fin (size M),
      isR1CSRow ((toElements (M := M) x)[i.val] - (toElements (M := M) y)[i.val])) :
    IsR1CSCirc (assertEquals x y) := by
  refine IsR1CSCirc.assertion fun n => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := M) (x, y)).operations n)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (F := F circomPrime) (α := Expression (F circomPrime))
    (m := size M) fun i k => ?_) n
  refine IsR1CSCirc.assertZero ?_ k
  simpa only [Vector.getElem_map, Vector.getElem_zip] using hrow i

theorem r1cs_assertEquals_row (x y : Expression (F circomPrime))
    (hrow : isR1CSRow (x - y)) :
    IsR1CSCirc (Expression.assertEquals x y) := by
  refine r1cs_assertEqualsM (M := field) x y (fun i => ?_)
  simpa [explicit_provable_type] using hrow

theorem r1cs_assertEquals (x y : Expression (F circomPrime))
    (hx : Affine x) (hy : Affine y) :
    IsR1CSCirc (Expression.assertEquals x y) :=
  r1cs_assertEquals_row x y (isR1CSRow_of_affine (Affine.sub hx hy))

theorem usesIR_assertEqualsM {M : TypeMap} [ProvableType M] (x y : Var M (F circomPrime)) :
    UsesIRCirc (assertEquals x y) := by
  refine UsesIRCirc.assertion fun n => ?_
  show operationsUseIR ((Gadgets.Equality.main (M := M) (x, y)).operations n)
  unfold Gadgets.Equality.main
  exact (UsesIRCirc.forEach (m := size M) (fun a k => UsesIRCirc.assertZero _ k)) n

theorem usesIR_assertEquals (x y : Expression (F circomPrime)) :
    UsesIRCirc (Expression.assertEquals x y) :=
  usesIR_assertEqualsM (M := field) x y

theorem costIs_assignEq (rhs : Expression (F circomPrime)) :
    CostIs (HasAssignEq.assignEq rhs) ⟨1, 1⟩ := by
  change CostIs (do
    let w ← Circuit.witnessField (.expr rhs)
    Expression.assertEquals w rhs
    pure w) ⟨1, 1⟩
  exact CostIs.bind (CostIs.witnessField (F := F circomPrime) (.expr rhs)) fun w =>
    CostIs.bind (costIs_assertEquals w rhs) fun _ => CostIs.pure w

theorem r1cs_assignEq_row (rhs : Expression (F circomPrime))
    (hrow : ∀ off, isR1CSRow ((Circuit.witnessField (.expr rhs)).output off + -rhs)) :
    IsR1CSCirc (HasAssignEq.assignEq rhs) := by
  change IsR1CSCirc (do
    let w ← Circuit.witnessField (.expr rhs)
    Expression.assertEquals w rhs
    pure w)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun off => ?_
  exact IsR1CSCirc.bind (r1cs_assertEquals_row _ rhs (hrow off)) fun _ => IsR1CSCirc.pure _

theorem r1cs_assignEq (rhs : Expression (F circomPrime)) (hrhs : Affine rhs) :
    IsR1CSCirc (HasAssignEq.assignEq rhs) :=
  r1cs_assignEq_row rhs fun off =>
    isR1CSRow_of_affine
      (Affine.add (affine_witnessField_output _ off) (Affine.neg hrhs))

theorem usesIR_assignEq (rhs : Expression (F circomPrime)) :
    UsesIRCirc (HasAssignEq.assignEq rhs) := by
  change UsesIRCirc (do
    let w ← Circuit.witnessField (.expr rhs)
    Expression.assertEquals w rhs
    pure w)
  exact UsesIRCirc.bind (UsesIRCirc.witnessField _) fun w =>
    UsesIRCirc.bind (usesIR_assertEquals w rhs) fun _ => UsesIRCirc.pure w

/-! ## Witnessed multiplication

`Mul.main` allocates one field witness and constrains it with one product row. -/

def mulCost : Count := ⟨1, 1⟩

theorem costIs_mul (input : Var Mul.Inputs (F circomPrime)) :
    CostIs (Mul.main input) mulCost :=
  CostIs.bind (CostIs.witnessField _) fun product =>
    CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure product

theorem costIs_sub_mul (input : Var Mul.Inputs (F circomPrime)) :
    CostIs (subcircuit Mul.circuit input) mulCost :=
  CostIs.subcircuit (costIs_mul _)

theorem usesIR_mul (input : Var Mul.Inputs (F circomPrime)) :
    UsesIRCirc (Mul.main input) :=
  UsesIRCirc.bind (UsesIRCirc.witnessField _) fun product =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ => UsesIRCirc.pure product

theorem usesIR_sub_mul (input : Var Mul.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuit Mul.circuit input) :=
  UsesIRCirc.subcircuit (usesIR_mul _)

/-! The R1CS predicates are intentionally opaque from here on: the proofs construct
their certificates with the single-row lemmas and never need to evaluate the predicate
on a neutral circuit expression. -/
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS
attribute [local irreducible] operationsUseIR flatOperationsUseIR IsIR

/-- A degree-0 (constant) form times a degree-≤1 form is affine. -/
theorem Affine.deg0_mul {a b : Expression (F circomPrime)} (ha : degree a = 0)
    (hb : Affine b) : Affine (a * b) := by
  simp only [Affine, degree_mul, ha, Nat.zero_add]; exact hb

/-! `Affine e` unfolds to `degree e ≤ 1`, and every *failing* affineness attempt then
makes `isDefEq` evaluate `degree` over the whole expression tree. On a gadget with
hundreds of rows that alone costs minutes, so the predicate is sealed here: from now on
affineness is only ever built from the lemmas above, never from its definition. -/
attribute [local irreducible] Affine

theorem affine_mul_output (input : Var Mul.Inputs (F circomPrime)) (n : ℕ) :
    Affine ((Mul.main input).output n) := by
  simp only [Mul.main, circuit_norm]
  exact Affine.var _

theorem affine_sub_mul_output (input : Var Mul.Inputs (F circomPrime)) (n : ℕ) :
    Affine ((subcircuit Mul.circuit input).output n) := by
  change Affine (Expression.var _)
  exact Affine.var _

theorem r1cs_mul (input : Var Mul.Inputs (F circomPrime))
    (ha : Affine input.a) (hb : Affine input.b) :
    IsR1CSCirc (Mul.main input) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.assertZero
        (isR1CSRow_sub_mul (affine_witnessField_output _ n) ha hb))
      (fun _ => IsR1CSCirc.pure _)

theorem r1cs_sub_mul (input : Var Mul.Inputs (F circomPrime))
    (ha : Affine input.a) (hb : Affine input.b) :
    IsR1CSCirc (subcircuit Mul.circuit input) :=
  IsR1CSCirc.subcircuit (r1cs_mul input ha hb)

/-! ### Extra single-row shapes

`isR1CSRow_sub_mul` covers `C - A*B`; the extractor's gadgets also emit the mirrored
`A*B - C` and the `C - (A*B + D)` shape of circomlib's `IsZero`. -/

theorem isR1CSRow_mul_sub {A B C : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) : isR1CSRow (A * B - C) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (A * B + -C) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (A * B + -C) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)

theorem isR1CSRow_sub_mul_add {C A B D : Expression (F circomPrime)}
    (hC : Affine C) (hA : Affine A) (hB : Affine B) (hD : Affine D) :
    isR1CSRow (C - (A * B + D)) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (C + -(A * B + D)) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add,
            r1csProducts_of_affine hC, r1csProducts_of_affine hD, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (C + -(A * B + D)) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add,
            r1csProducts_of_affine hC, r1csProducts_of_affine hD, h]) (by omega)

/-! ## Bit decomposition (`Num2Bits`)

`Num2Bits` is the leaf beneath circomlib's comparison gadgets. Its public
`GeneralFormalCircuit` wrapper exposes the same `main` operation tree. -/

theorem costIs_num2Bits (n : ℕ) (x : Expression (F circomPrime)) :
    CostIs (Num2Bits.main n x) ⟨n, n + 1⟩ := by
  unfold Num2Bits.main
  have hcount : (⟨n, 0⟩ + (⟨n * 0, n * 1⟩ + ⟨0, 1⟩) : Count) = ⟨n, n + 1⟩ := by
    show (⟨_, _⟩ : Count) = _
    congr 1
    simp
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) n _) fun bits => ?_
  refine CostIs.bind (CostIs.foldlRange (K := ⟨0, 1⟩) (init := (0, 1))
    (body := fun (lc1, e2) i => do
      bits[i] * (bits[i] - 1) === 0
      let lc1 := lc1 + bits[i] * e2
      return (lc1, e2 + e2))
    fun s i m => ?_) fun p => ?_
  · simpa [Count.add_zero, HasAssertEq.assert_eq] using
      ((CostIs.bind (costIs_assertEquals (bits[i] * (bits[i] - 1)) 0) fun _ =>
        CostIs.pure (s.1 + bits[i] * s.2, s.2 + s.2)) m)
  · obtain ⟨lc1, e2⟩ := p
    exact CostIs.bind (costIs_assertEquals lc1 x) fun _ => CostIs.pure bits

theorem usesIR_num2Bits (n : ℕ) (x : Expression (F circomPrime)) :
    UsesIRCirc (Num2Bits.main n x) := by
  unfold Num2Bits.main
  refine UsesIRCirc.bind (UsesIRCirc.witnessVector (F := F circomPrime) n _) fun bits => ?_
  refine UsesIRCirc.bind (UsesIRCirc.foldlRange fun s i m => ?_) fun p => ?_
  · exact (UsesIRCirc.bind (usesIR_assertEquals _ _) fun _ => UsesIRCirc.pure _) m
  · obtain ⟨lc1, e2⟩ := p
    exact UsesIRCirc.bind (usesIR_assertEquals lc1 x) fun _ => UsesIRCirc.pure bits

theorem affine_fieldFromBitsExpr {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (h : AffineW bits) : Affine (fieldFromBitsExpr bits) := by
  unfold fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

theorem r1cs_assertEquals_bitBoolean (bit : Expression (F circomPrime))
    (hbit : Affine bit) :
    IsR1CSCirc (bit * (bit - 1) === 0) :=
  r1cs_assertEquals_row _ _
    (isR1CSRow_mul_sub hbit (Affine.sub hbit (Affine.const 1)) Affine.zero)

theorem r1cs_num2Bits (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Num2Bits.main n x) := by
  unfold Num2Bits.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector n _) fun bitsOff => ?_
  let bits : Var (fields n) (F circomPrime) := varFromOffset (fields n) bitsOff
  have hbits : AffineW bits := affineW_varFromOffset n bitsOff
  let body : (Expression (F circomPrime) × Expression (F circomPrime)) → Fin n →
      Circuit (F circomPrime) (Expression (F circomPrime) × Expression (F circomPrime)) :=
    fun (lc1, e2) i => do
      bits[i] * (bits[i] - 1) === 0
      let lc1 := lc1 + bits[i] * e2
      return (lc1, e2 + e2)
  let P : Expression (F circomPrime) × Expression (F circomPrime) → Prop :=
    fun s => Affine s.1 ∧ degree s.2 = 0
  have hinit : P (0, 1) := ⟨Affine.zero, degree_const _⟩
  have hbody : ∀ s i, P s → IsR1CSCirc (body s i) := by
    intro s i hs
    dsimp [body]
    exact IsR1CSCirc.bind (r1cs_assertEquals_bitBoolean _ (hbits i.val i.isLt)) fun _ =>
      IsR1CSCirc.pure _
  have hstep : ∀ s (i : Fin n) k, P s → P ((body s i).output k) := by
    intro s i k hs
    dsimp [body]
    simp only [circuit_norm]
    exact ⟨Affine.add hs.1 (Affine.mul_deg0 (hbits i.val i.isLt) hs.2), by
      rw [degree_add, hs.2, max_self]⟩
  let constant : Circuit.ConstantLength fun (t :
      (Expression (F circomPrime) × Expression (F circomPrime)) × Fin n) => body t.1 t.2 := by
    apply Circuit.ConstantLength.fromConstantLength'
    intros
    simp only [body, circuit_norm]
  let loop := Circuit.foldlRange n (0, 1) body constant
  have hloop : IsR1CSCirc loop :=
    IsR1CSCirc.foldlRange_inv P hinit hbody hstep
  refine IsR1CSCirc.bind_out hloop fun loopOff => ?_
  have hout : P (loop.output loopOff) := by
    rw [show loop = Circuit.foldlRange n (0, 1) body constant from rfl,
      Circuit.foldlRange.output_eq]
    apply finFoldl_invariant P _ _ hinit
    intro s i hs
    exact hstep s i _ hs
  dsimp [loop, body] at hout ⊢
  exact IsR1CSCirc.bind (r1cs_assertEquals _ x hout.1 hx) fun _ =>
    IsR1CSCirc.pure _

theorem costIs_assertion_num2Bits (n : ℕ) (hn : 2 ^ n < circomPrime)
    (x : Var field (F circomPrime)) :
    CostIs (subcircuitWithAssertion (Num2Bits.circuit n hn) x) ⟨n, n + 1⟩ := by
  apply CostIs.subcircuitWithAssertion
  intro m
  simpa only [Num2Bits.circuit] using
    (CostIs.subcircuitWithAssertion
      (circuit := Num2Bits.arbitraryBitLengthCircuit n) (b := x)
      (K := ⟨n, n + 1⟩) (fun k => costIs_num2Bits n x k) m)

theorem r1cs_assertion_num2Bits (n : ℕ) (hn : 2 ^ n < circomPrime)
    (x : Var field (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (subcircuitWithAssertion (Num2Bits.circuit n hn) x) := by
  apply IsR1CSCirc.subcircuitWithAssertion
  intro m
  simpa only [Num2Bits.circuit] using
    (IsR1CSCirc.subcircuitWithAssertion
      (circuit := Num2Bits.arbitraryBitLengthCircuit n) (b := x)
      (fun k => r1cs_num2Bits n x hx k) m)

theorem usesIR_assertion_num2Bits (n : ℕ) (hn : 2 ^ n < circomPrime)
    (x : Var field (F circomPrime)) :
    UsesIRCirc (subcircuitWithAssertion (Num2Bits.circuit n hn) x) := by
  apply UsesIRCirc.subcircuitWithAssertion
  intro m
  simpa only [Num2Bits.circuit] using
    (UsesIRCirc.subcircuitWithAssertion
      (circuit := Num2Bits.arbitraryBitLengthCircuit n) (b := x)
      (fun k => usesIR_num2Bits n x k) m)

/-! ## Zero and equality comparators

`IsZero` has two fresh fields: the inverse hint and the public output. The output
equality has a quadratic right-hand side, so it cannot use the affine `<==` bridge;
the proof below certifies that row directly. `IsEqual` is the `IsZero` subcircuit on
the affine difference of its two inputs. -/

def isZeroCost : Count := ⟨2, 2⟩

theorem costIs_isZero (input : Expression (F circomPrime)) :
    CostIs (IsZero.main input) isZeroCost := by
  unfold IsZero.main isZeroCost
  exact CostIs.bind (CostIs.witnessField _) fun inv =>
    CostIs.bind (costIs_assignEq (-input * inv + 1)) fun out =>
      CostIs.bind (costIs_assertEquals (input * out) 0) fun _ => CostIs.pure out

theorem costIs_sub_isZero (input : Expression (F circomPrime)) :
    CostIs (subcircuit IsZero.circuit input) isZeroCost :=
  CostIs.subcircuit (costIs_isZero input)

theorem usesIR_isZero (input : Expression (F circomPrime)) :
    UsesIRCirc (IsZero.main input) := by
  unfold IsZero.main
  exact UsesIRCirc.bind (UsesIRCirc.witnessField _) fun inv =>
    UsesIRCirc.bind (usesIR_assignEq (-input * inv + 1)) fun out =>
      UsesIRCirc.bind (usesIR_assertEquals (input * out) 0) fun _ => UsesIRCirc.pure out

theorem usesIR_sub_isZero (input : Expression (F circomPrime)) :
    UsesIRCirc (subcircuit IsZero.circuit input) :=
  UsesIRCirc.subcircuit (usesIR_isZero input)

theorem r1cs_isZero (input : Expression (F circomPrime)) (hinput : Affine input) :
    IsR1CSCirc (IsZero.main input) := by
  unfold IsZero.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun invOff => ?_
  set inv := (Circuit.witnessField (F := F circomPrime)
    (.ite (input =? 0) 0 input⁻¹)).output invOff with hinvdef
  have hinv : Affine inv := affine_witnessField_output _ invOff
  refine IsR1CSCirc.bind_out (r1cs_assignEq_row (-input * inv + 1) ?_) fun outOff => ?_
  · intro off
    exact isR1CSRow_sub_mul_add (affine_witnessField_output _ off)
      (Affine.neg hinput) hinv (Affine.const 1)
  · set out := (Circuit.witnessField (F := F circomPrime)
      (.expr (-input * inv + 1))).output outOff with houtdef
    have hout : Affine out := affine_witnessField_output _ outOff
    exact IsR1CSCirc.bind
      (r1cs_assertEquals_row (input * out) 0
        (isR1CSRow_mul_sub hinput hout Affine.zero))
      fun _ => IsR1CSCirc.pure _

theorem r1cs_sub_isZero (input : Expression (F circomPrime)) (hinput : Affine input) :
    IsR1CSCirc (subcircuit IsZero.circuit input) :=
  IsR1CSCirc.subcircuit (r1cs_isZero input hinput)

theorem affine_sub_isZero_output (input : Expression (F circomPrime)) (off : ℕ) :
    Affine ((subcircuit IsZero.circuit input).output off) := by
  change Affine (Expression.var _)
  exact Affine.var _

theorem costIs_isEqual (input : Expression (F circomPrime) × Expression (F circomPrime)) :
    CostIs (IsEqual.main input) isZeroCost := by
  unfold IsEqual.main
  exact CostIs.bind (costIs_sub_isZero (input.1 - input.2)) fun out => CostIs.pure out

theorem costIs_sub_isEqual (input : Var fieldPair (F circomPrime)) :
    CostIs (subcircuit IsEqual.circuit input) isZeroCost :=
  CostIs.subcircuit (costIs_isEqual input)

theorem usesIR_isEqual (input : Expression (F circomPrime) × Expression (F circomPrime)) :
    UsesIRCirc (IsEqual.main input) := by
  unfold IsEqual.main
  exact UsesIRCirc.bind (usesIR_sub_isZero (input.1 - input.2)) fun out => UsesIRCirc.pure out

theorem usesIR_sub_isEqual (input : Var fieldPair (F circomPrime)) :
    UsesIRCirc (subcircuit IsEqual.circuit input) :=
  UsesIRCirc.subcircuit (usesIR_isEqual input)

theorem r1cs_isEqual (input : Expression (F circomPrime) × Expression (F circomPrime))
    (hleft : Affine input.1) (hright : Affine input.2) :
    IsR1CSCirc (IsEqual.main input) := by
  unfold IsEqual.main
  exact r1cs_sub_isZero (input.1 - input.2) (Affine.sub hleft hright)

theorem r1cs_sub_isEqual (input : Var fieldPair (F circomPrime))
    (hleft : Affine input.1) (hright : Affine input.2) :
    IsR1CSCirc (subcircuit IsEqual.circuit input) :=
  IsR1CSCirc.subcircuit (r1cs_isEqual input hleft hright)

theorem affine_sub_isEqual_output (input : Var fieldPair (F circomPrime)) (off : ℕ) :
    Affine ((subcircuit IsEqual.circuit input).output off) := by
  change Affine (Expression.var _)
  exact Affine.var _

/-! ## `LessThan`

`LessThan n` decomposes `x + 2^n - y` into `n + 1` bits and allocates its output as an
equality to the high-bit complement: `⟨n + 1, n + 2⟩` plus one witnessed equality. -/

def lessThanCost (n : ℕ) : Count := ⟨n + 2, n + 3⟩

theorem costIs_lessThan (n : ℕ) (hn : 2 ^ (n + 1) < circomPrime)
    (input : Var fieldPair (F circomPrime)) :
    CostIs (LessThan.main n hn input) (lessThanCost n) := by
  unfold LessThan.main lessThanCost
  exact CostIs.bind
    (costIs_assertion_num2Bits (n + 1) hn
      (input.1 + (2 ^ n : F circomPrime) - input.2)) fun bits =>
    CostIs.bind (costIs_assignEq (1 - bits[n])) fun out => CostIs.pure out

theorem costIs_sub_lessThan (n : ℕ) (hn : 2 ^ (n + 1) < circomPrime)
    (input : Var fieldPair (F circomPrime)) :
    CostIs (subcircuit (LessThan.circuit n hn) input) (lessThanCost n) :=
  CostIs.subcircuit (fun k => costIs_lessThan n hn input k)

theorem usesIR_lessThan (n : ℕ) (hn : 2 ^ (n + 1) < circomPrime)
    (input : Var fieldPair (F circomPrime)) :
    UsesIRCirc (LessThan.main n hn input) := by
  unfold LessThan.main
  refine UsesIRCirc.bind
    (usesIR_assertion_num2Bits (n + 1) hn
      (input.1 + (2 ^ n : F circomPrime) - input.2)) fun bits => ?_
  exact UsesIRCirc.bind (f := HasAssignEq.assignEq (1 - bits[n]))
    (usesIR_assignEq (1 - bits[n])) fun out => UsesIRCirc.pure out

theorem usesIR_sub_lessThan (n : ℕ) (hn : 2 ^ (n + 1) < circomPrime)
    (input : Var fieldPair (F circomPrime)) :
    UsesIRCirc (subcircuit (LessThan.circuit n hn) input) :=
  UsesIRCirc.subcircuit (fun k => usesIR_lessThan n hn input k)

theorem r1cs_lessThan (n : ℕ) (hn : 2 ^ (n + 1) < circomPrime)
    (input : Var fieldPair (F circomPrime))
    (hx : Affine input.1) (hy : Affine input.2) :
    IsR1CSCirc (LessThan.main n hn input) := by
  unfold LessThan.main
  refine IsR1CSCirc.bind_out
    (r1cs_assertion_num2Bits (n + 1) hn
      (input.1 + (2 ^ n : F circomPrime) - input.2)
      (Affine.sub (Affine.add hx (Affine.const _)) hy)) fun bitsOff => ?_
  have hbit : Affine (((subcircuitWithAssertion (Num2Bits.circuit (n + 1) hn)
      (input.1 + (2 ^ n : F circomPrime) - input.2)).output bitsOff)[n]) := by
    show Affine ((varFromOffset (fields (n + 1)) bitsOff :
      Var (fields (n + 1)) (F circomPrime))[n])
    exact affineW_varFromOffset (n + 1) bitsOff n (by omega)
  exact r1cs_assignEq _ (Affine.sub (Affine.const 1) hbit)

theorem r1cs_sub_lessThan (n : ℕ) (hn : 2 ^ (n + 1) < circomPrime)
    (input : Var fieldPair (F circomPrime))
    (hx : Affine input.1) (hy : Affine input.2) :
    IsR1CSCirc (subcircuit (LessThan.circuit n hn) input) :=
  IsR1CSCirc.subcircuit (fun k => r1cs_lessThan n hn input hx hy k)

theorem affine_sub_lessThan_output (n : ℕ) (hn : 2 ^ (n + 1) < circomPrime)
    (input : Var fieldPair (F circomPrime)) (off : ℕ) :
    Affine ((subcircuit (LessThan.circuit n hn) input).output off) := by
  change Affine (Expression.var _)
  exact Affine.var _

/-! ## Length flags

`LenFlags.main` has no witnesses: one booleanity row per flag, then the affine
sum-to-one and weighted-length rows. -/

def lenFlagsCost : Count := ⟨0, flagLen + 2⟩

theorem costIs_lenFlags (input : Var LenFlags.Inputs (F circomPrime)) :
    CostIs (LenFlags.main input) lenFlagsCost := by
  unfold LenFlags.main lenFlagsCost
  exact CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ => CostIs.assertZero _

theorem costIs_assertion_lenFlags (input : Var LenFlags.Inputs (F circomPrime)) :
    CostIs (assertion LenFlags.circuit input) lenFlagsCost :=
  CostIs.assertion (costIs_lenFlags input)

theorem usesIR_lenFlags (input : Var LenFlags.Inputs (F circomPrime)) :
    UsesIRCirc (LenFlags.main input) := by
  unfold LenFlags.main
  exact UsesIRCirc.bind (UsesIRCirc.forEach fun _ n => UsesIRCirc.assertZero _ n) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ => UsesIRCirc.assertZero _

theorem usesIR_assertion_lenFlags (input : Var LenFlags.Inputs (F circomPrime)) :
    UsesIRCirc (assertion LenFlags.circuit input) :=
  UsesIRCirc.assertion (usesIR_lenFlags input)

theorem r1cs_lenFlags (input : Var LenFlags.Inputs (F circomPrime))
    (hlen : Affine input.len) (hflags : AffineW input.lenFlags) :
    IsR1CSCirc (LenFlags.main input) := by
  unfold LenFlags.main
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_mul (hflags i.val i.isLt)
      (Affine.sub (hflags i.val i.isLt) (Affine.const 1))) k
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.assertZero ?_
  · exact isR1CSRow_of_affine
      (Affine.sub
        (affine_finFoldl' (fun acc i => acc + input.lenFlags[i]) 0 Affine.zero
          (fun acc i h => Affine.add h (hflags i.val i.isLt)))
        (Affine.const 1))
  · exact isR1CSRow_of_affine
      (Affine.sub hlen
        (affine_finFoldl'
          (fun acc i => acc + input.lenFlags[i] *
            (((i.val : ℕ) : F circomPrime) : Expression (F circomPrime)))
          0 Affine.zero
          (fun acc i h => Affine.add h
            (Affine.mul_deg0 (hflags i.val i.isLt) (degree_const _)))))

theorem r1cs_assertion_lenFlags (input : Var LenFlags.Inputs (F circomPrime))
    (hlen : Affine input.len) (hflags : AffineW input.lenFlags) :
    IsR1CSCirc (assertion LenFlags.circuit input) :=
  IsR1CSCirc.assertion (r1cs_lenFlags input hlen hflags)

/-! ## One-hot of a small value -/

def oneHotCost (n : ℕ) : Count := ⟨n, n + 2⟩

theorem costIs_oneHot (n : ℕ) [NeZero n] (inp : Var OneHot.Inputs (F circomPrime)) :
    CostIs (OneHot.main n inp) (oneHotCost n) := by
  unfold OneHot.main
  have hcount : ((⟨n, 0⟩ : Count) + (⟨n * 0, n * 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + Count.zero))))
      = oneHotCost n :=
    Count.ext' (by simp [oneHotCost, Count.zero]) (by simp [oneHotCost, Count.zero])
  rw [← hcount]
  exact CostIs.bind (CostIs.witnessVector n _) fun flags =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure flags

theorem costIs_sub_oneHot (n : ℕ) [NeZero n] (inp : Var OneHot.Inputs (F circomPrime)) :
    CostIs (subcircuit (OneHot.circuit n) inp) (oneHotCost n) :=
  CostIs.subcircuit (costIs_oneHot n inp)

theorem usesIR_oneHot (n : ℕ) [NeZero n] (inp : Var OneHot.Inputs (F circomPrime)) :
    UsesIRCirc (OneHot.main n inp) := by
  unfold OneHot.main
  exact UsesIRCirc.bind (UsesIRCirc.witnessVector n _) fun flags =>
    UsesIRCirc.bind (UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ => UsesIRCirc.pure flags

theorem usesIR_sub_oneHot (n : ℕ) [NeZero n] (inp : Var OneHot.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuit (OneHot.circuit n) inp) :=
  UsesIRCirc.subcircuit (usesIR_oneHot n inp)

theorem r1cs_oneHot (n : ℕ) [NeZero n] (inp : Var OneHot.Inputs (F circomPrime))
    (hx : Affine inp.x) :
    IsR1CSCirc (OneHot.main n inp) := by
  unfold OneHot.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector n _) fun off => ?_
  have hflags : AffineW ((Circuit.witnessVector (F := F circomPrime) n
      (.range n fun i => (i =? inp.x.val).toField)).output off) :=
    affineW_witnessVector_output _ _ _
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_mul (hflags i.val i.isLt)
      (Affine.sub (hflags i.val i.isLt) (Affine.const 1))) k
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
  · exact isR1CSRow_of_affine
      (Affine.sub (affine_finFoldl' _ 0 Affine.zero
        (fun acc i h => Affine.add h (hflags i.val i.isLt))) (Affine.const 1))
  · exact isR1CSRow_of_affine
      (Affine.sub hx (affine_finFoldl' _ 0 Affine.zero
        (fun acc i h => Affine.add h
          (Affine.mul_deg0 (hflags i.val i.isLt) (degree_const _)))))

theorem r1cs_sub_oneHot (n : ℕ) [NeZero n] (inp : Var OneHot.Inputs (F circomPrime))
    (hx : Affine inp.x) :
    IsR1CSCirc (subcircuit (OneHot.circuit n) inp) :=
  IsR1CSCirc.subcircuit (r1cs_oneHot n inp hx)

theorem affineW_sub_oneHot_output (n : ℕ) [NeZero n]
    (inp : Var OneHot.Inputs (F circomPrime)) (off : ℕ) :
    AffineW ((subcircuit (OneHot.circuit n) inp).output off) := by
  show AffineW (varFromOffset (fields n) off : Var (fields n) (F circomPrime))
  exact affineW_varFromOffset n off

/-! ## Filled-prefix mask -/

def filledMaskCost (n : ℕ) : Count := ⟨n, 3 * n + 1⟩

theorem costIs_filledMask (n : ℕ) [NeZero n] (inp : Var (FilledMask.Inputs n) (F circomPrime)) :
    CostIs (FilledMask.main n inp) (filledMaskCost n) := by
  unfold FilledMask.main
  have hcount : ((⟨n, 0⟩ : Count) + (⟨n * 0, n * 1⟩ + (⟨n * 0, n * 1⟩ +
      (⟨0, 1⟩ + ⟨n * 0, n * 1⟩)))) = filledMaskCost n :=
    Count.ext' (by simp [filledMaskCost]) (by simp [filledMaskCost]; omega)
  rw [← hcount]
  exact CostIs.bind (CostIs.witnessVector n _) fun filled =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.forEach fun _ => CostIs.assertZero _

theorem costIs_assertion_filledMask (n : ℕ) [NeZero n]
    (inp : Var (FilledMask.Inputs n) (F circomPrime)) :
    CostIs (assertion (FilledMask.circuit n) inp) (filledMaskCost n) :=
  CostIs.assertion (costIs_filledMask n inp)

theorem usesIR_filledMask (n : ℕ) [NeZero n]
    (inp : Var (FilledMask.Inputs n) (F circomPrime)) :
    UsesIRCirc (FilledMask.main n inp) := by
  unfold FilledMask.main
  exact UsesIRCirc.bind (UsesIRCirc.witnessVector n _) fun filled =>
    UsesIRCirc.bind (UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k

theorem usesIR_assertion_filledMask (n : ℕ) [NeZero n]
    (inp : Var (FilledMask.Inputs n) (F circomPrime)) :
    UsesIRCirc (assertion (FilledMask.circuit n) inp) :=
  UsesIRCirc.assertion (usesIR_filledMask n inp)

theorem r1cs_filledMask (n : ℕ) [NeZero n] (inp : Var (FilledMask.Inputs n) (F circomPrime))
    (hlen : Affine inp.len) (hcells : AffineW inp.cells) :
    IsR1CSCirc (FilledMask.main n inp) := by
  unfold FilledMask.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector n _) fun off => ?_
  have hf : AffineW ((Circuit.witnessVector (F := F circomPrime) n
      (.range n fun t => (t <? inp.len.val).toField)).output off) :=
    affineW_witnessVector_output _ _ _
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_mul (hf i.val i.isLt)
      (Affine.sub (hf i.val i.isLt) (Affine.const 1))) k
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_mul (hf i.val i.isLt)
      (Affine.sub (Affine.const 1) (hf (i.val - 1) (by have := i.isLt; omega)))) k
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => ?_
  · exact isR1CSRow_of_affine
      (Affine.sub (affine_finFoldl' _ 0 Affine.zero
        (fun acc i h => Affine.add h (hf i.val i.isLt))) hlen)
  refine IsR1CSCirc.forEach_mem fun i k => ?_
  simp only [Vector.getElem_finRange]
  exact IsR1CSCirc.assertZero (isR1CSRow_mul (hcells i.val i.isLt)
    (Affine.sub (Affine.const 1) (hf i.val i.isLt))) k

theorem r1cs_assertion_filledMask (n : ℕ) [NeZero n]
    (inp : Var (FilledMask.Inputs n) (F circomPrime))
    (hlen : Affine inp.len) (hcells : AffineW inp.cells) :
    IsR1CSCirc (assertion (FilledMask.circuit n) inp) :=
  IsR1CSCirc.assertion (r1cs_filledMask n inp hlen hcells)

/-! ## `Circuit.map` combinators

`Circuit.map` is the value-returning loop former the automata and `RouteSlot` use. -/

theorem IsR1CSCirc.mapVec_mem {F : Type} [FiniteField F] {α β : Type} {m : ℕ}
    [Inhabited α] {xs : Vector α m} {body : α → Circuit F β}
    {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.map xs body constant) := by
  intro n
  rw [Circuit.map.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)

theorem UsesIRCirc.mapVec {F : Type} [FiniteField F] {α β : Type} {m : ℕ}
    [Inhabited α] {xs : Vector α m} {body : α → Circuit F β}
    {constant : Circuit.ConstantLength body}
    (h : ∀ a n, operationsUseIR ((body a).operations n)) :
    UsesIRCirc (Circuit.map xs body constant) := by
  intro n
  rw [Circuit.map.operations_eq]
  exact operationsUseIR_flatten_ofFn _ (fun i => h _ _)

theorem affineW_map_output {α : Type} [Inhabited α] {m : ℕ} (xs : Vector α m)
    (body : α → Circuit (F circomPrime) (Expression (F circomPrime)))
    (constant : Circuit.ConstantLength body)
    (h : ∀ a n, Affine ((body a).output n)) (n : ℕ) :
    AffineW ((Circuit.map xs body constant).output n) := by
  intro i hi
  rw [Circuit.map.output_eq, Vector.getElem_mapIdx]
  exact h _ _

/-! ## Anchors: the initial register block -/

def anchorsCost : Count := ⟨0, 7 + 2 * Model.nClaims⟩

theorem costIs_anchors (inp : Var Anchors.Inputs (F circomPrime)) :
    CostIs (Anchors.main inp) anchorsCost := by
  unfold Anchors.main anchorsCost
  exact CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.forEach fun _ => CostIs.assertZero _

theorem costIs_assertion_anchors (inp : Var Anchors.Inputs (F circomPrime)) :
    CostIs (assertion Anchors.circuit inp) anchorsCost :=
  CostIs.assertion (costIs_anchors inp)

theorem usesIR_anchors (inp : Var Anchors.Inputs (F circomPrime)) :
    UsesIRCirc (Anchors.main inp) := by
  unfold Anchors.main
  exact UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k) fun _ =>
    UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k

theorem usesIR_assertion_anchors (inp : Var Anchors.Inputs (F circomPrime)) :
    UsesIRCirc (assertion Anchors.circuit inp) :=
  UsesIRCirc.assertion (usesIR_anchors inp)

theorem r1cs_anchors (inp : Var Anchors.Inputs (F circomPrime))
    (haccm : Affine inp.accm) (hst : AffineW inp.st) (hsub : AffineW inp.sub)
    (hhex : Affine inp.hexAcc) (hkIdx : Affine inp.kIdx) (hofs : Affine inp.ofs)
    (hnMem : Affine inp.nMem) (hm : AffineW inp.m) (hclaim : AffineW inp.claim) :
    IsR1CSCirc (Anchors.main inp) := by
  unfold Anchors.main
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine haccm)) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub (hst _ (by decide)) (Affine.const 1)))) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub (hsub _ (by decide)) (Affine.const 1)))) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine hhex)) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine hkIdx)) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine hofs)) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine hnMem)) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ =>
    IsR1CSCirc.forEach_mem fun i k => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_of_affine (hm i.val i.isLt)) k
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_of_affine (hclaim i.val i.isLt)) k

theorem r1cs_assertion_anchors (inp : Var Anchors.Inputs (F circomPrime))
    (haccm : Affine inp.accm) (hst : AffineW inp.st) (hsub : AffineW inp.sub)
    (hhex : Affine inp.hexAcc) (hkIdx : Affine inp.kIdx) (hofs : Affine inp.ofs)
    (hnMem : Affine inp.nMem) (hm : AffineW inp.m) (hclaim : AffineW inp.claim) :
    IsR1CSCirc (assertion Anchors.circuit inp) :=
  IsR1CSCirc.assertion
    (r1cs_anchors inp haccm hst hsub hhex hkIdx hofs hnMem hm hclaim)

/-! ## Acceptance: the final register block and the member cap -/

def acceptanceCost : Count := ⟨Acceptance.memWidth, Acceptance.memWidth + 4⟩

theorem costIs_acceptance (inp : Var Acceptance.Inputs (F circomPrime)) :
    CostIs (Acceptance.main inp) acceptanceCost := by
  unfold Acceptance.main acceptanceCost
  exact CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.witnessVector Acceptance.memWidth _) fun flags =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ => CostIs.assertZero _

theorem costIs_assertion_acceptance (inp : Var Acceptance.Inputs (F circomPrime)) :
    CostIs (assertion Acceptance.circuit inp) acceptanceCost :=
  CostIs.assertion (costIs_acceptance inp)

theorem usesIR_acceptance (inp : Var Acceptance.Inputs (F circomPrime)) :
    UsesIRCirc (Acceptance.main inp) := by
  unfold Acceptance.main
  exact UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.witnessVector Acceptance.memWidth _) fun flags =>
    UsesIRCirc.bind (UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ => UsesIRCirc.assertZero _

theorem usesIR_assertion_acceptance (inp : Var Acceptance.Inputs (F circomPrime)) :
    UsesIRCirc (assertion Acceptance.circuit inp) :=
  UsesIRCirc.assertion (usesIR_acceptance inp)

theorem r1cs_acceptance (inp : Var Acceptance.Inputs (F circomPrime))
    (hst : AffineW inp.st) (hsub : AffineW inp.sub) (hnMem : Affine inp.nMem) :
    IsR1CSCirc (Acceptance.main inp) := by
  unfold Acceptance.main
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
    (Affine.sub (hst _ (by decide)) (Affine.const 1)))) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub (hsub _ (by decide)) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector Acceptance.memWidth _) fun off => ?_
  have hf : AffineW ((Circuit.witnessVector (F := F circomPrime) Acceptance.memWidth
      (.range Acceptance.memWidth fun i => (i =? inp.nMem.val).toField)).output off) :=
    affineW_witnessVector_output _ _ _
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_mul (hf i.val i.isLt)
      (Affine.sub (hf i.val i.isLt) (Affine.const 1))) k
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.assertZero ?_
  · exact isR1CSRow_of_affine
      (Affine.sub (affine_finFoldl' _ 0 Affine.zero
        (fun acc i h => Affine.add h (hf i.val i.isLt))) (Affine.const 1))
  · exact isR1CSRow_of_affine
      (Affine.sub hnMem (affine_finFoldl' _ 0 Affine.zero
        (fun acc i h => Affine.add h
          (Affine.mul_deg0 (hf i.val i.isLt) (degree_const _)))))

theorem r1cs_assertion_acceptance (inp : Var Acceptance.Inputs (F circomPrime))
    (hst : AffineW inp.st) (hsub : AffineW inp.sub) (hnMem : Affine inp.nMem) :
    IsR1CSCirc (assertion Acceptance.circuit inp) :=
  IsR1CSCirc.assertion (r1cs_acceptance inp hst hsub hnMem)

/-! ## The slot pins -/

def strSlotPinCost (n : ℕ) : Count := ⟨n, 3 * n + 4⟩
def intSlotPinCost (n : ℕ) : Count := ⟨n, 3 * n + 5⟩
def boolSlotPinCost : Count := ⟨0, 3⟩

theorem costIs_strSlotPin (n : ℕ) [NeZero n] (inp : Var (StrSlotPin.Inputs n) (F circomPrime)) :
    CostIs (StrSlotPin.main n inp) (strSlotPinCost n) := by
  unfold StrSlotPin.main
  have hcount : ((⟨0, 1⟩ : Count) + (⟨0, 1⟩ + (⟨0, 1⟩ + filledMaskCost n)))
      = strSlotPinCost n :=
    Count.ext' (by simp [strSlotPinCost, filledMaskCost])
      (by simp [strSlotPinCost, filledMaskCost]; omega)
  rw [← hcount]
  exact CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    costIs_assertion_filledMask n _

theorem costIs_assertion_strSlotPin (n : ℕ) [NeZero n]
    (inp : Var (StrSlotPin.Inputs n) (F circomPrime)) :
    CostIs (assertion (StrSlotPin.circuit n) inp) (strSlotPinCost n) :=
  CostIs.assertion (costIs_strSlotPin n inp)

theorem usesIR_strSlotPin (n : ℕ) [NeZero n]
    (inp : Var (StrSlotPin.Inputs n) (F circomPrime)) :
    UsesIRCirc (StrSlotPin.main n inp) := by
  unfold StrSlotPin.main
  exact UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    usesIR_assertion_filledMask n _

theorem usesIR_assertion_strSlotPin (n : ℕ) [NeZero n]
    (inp : Var (StrSlotPin.Inputs n) (F circomPrime)) :
    UsesIRCirc (assertion (StrSlotPin.circuit n) inp) :=
  UsesIRCirc.assertion (usesIR_strSlotPin n inp)

theorem r1cs_strSlotPin (n : ℕ) [NeZero n] (inp : Var (StrSlotPin.Inputs n) (F circomPrime))
    (hpresent : Affine inp.present) (hlen : Affine inp.len)
    (hsp : Affine inp.slot.present) (hsl : Affine inp.slot.len)
    (hbytes : AffineW inp.slot.bytes) :
    IsR1CSCirc (StrSlotPin.main n inp) := by
  unfold StrSlotPin.main
  exact IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hpresent
    (Affine.sub hpresent (Affine.const 1)))) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub hsp hpresent))) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub hsl hlen))) fun _ =>
    r1cs_assertion_filledMask n _ hlen hbytes

theorem r1cs_assertion_strSlotPin (n : ℕ) [NeZero n]
    (inp : Var (StrSlotPin.Inputs n) (F circomPrime))
    (hpresent : Affine inp.present) (hlen : Affine inp.len)
    (hsp : Affine inp.slot.present) (hsl : Affine inp.slot.len)
    (hbytes : AffineW inp.slot.bytes) :
    IsR1CSCirc (assertion (StrSlotPin.circuit n) inp) :=
  IsR1CSCirc.assertion (r1cs_strSlotPin n inp hpresent hlen hsp hsl hbytes)

theorem costIs_intSlotPin (n : ℕ) [NeZero n] (inp : Var (IntSlotPin.Inputs n) (F circomPrime)) :
    CostIs (IntSlotPin.main n inp) (intSlotPinCost n) := by
  unfold IntSlotPin.main
  have hcount : ((⟨0, 1⟩ : Count) + (⟨0, 1⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + filledMaskCost n))))
      = intSlotPinCost n :=
    Count.ext' (by simp [intSlotPinCost, filledMaskCost])
      (by simp [intSlotPinCost, filledMaskCost]; omega)
  rw [← hcount]
  exact CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    costIs_assertion_filledMask n _

theorem costIs_assertion_intSlotPin (n : ℕ) [NeZero n]
    (inp : Var (IntSlotPin.Inputs n) (F circomPrime)) :
    CostIs (assertion (IntSlotPin.circuit n) inp) (intSlotPinCost n) :=
  CostIs.assertion (costIs_intSlotPin n inp)

theorem usesIR_intSlotPin (n : ℕ) [NeZero n]
    (inp : Var (IntSlotPin.Inputs n) (F circomPrime)) :
    UsesIRCirc (IntSlotPin.main n inp) := by
  unfold IntSlotPin.main
  exact UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    usesIR_assertion_filledMask n _

theorem usesIR_assertion_intSlotPin (n : ℕ) [NeZero n]
    (inp : Var (IntSlotPin.Inputs n) (F circomPrime)) :
    UsesIRCirc (assertion (IntSlotPin.circuit n) inp) :=
  UsesIRCirc.assertion (usesIR_intSlotPin n inp)

theorem r1cs_intSlotPin (n : ℕ) [NeZero n] (inp : Var (IntSlotPin.Inputs n) (F circomPrime))
    (hpresent : Affine inp.present) (hneg : Affine inp.negative) (hlen : Affine inp.len)
    (hsp : Affine inp.slot.present) (hsn : Affine inp.slot.negative)
    (hsl : Affine inp.slot.len) (hdigits : AffineW inp.slot.digits) :
    IsR1CSCirc (IntSlotPin.main n inp) := by
  unfold IntSlotPin.main
  exact IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hpresent
    (Affine.sub hpresent (Affine.const 1)))) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub hsp hpresent))) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub hsn hneg))) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub hsl hlen))) fun _ =>
    r1cs_assertion_filledMask n _ hlen hdigits

theorem r1cs_assertion_intSlotPin (n : ℕ) [NeZero n]
    (inp : Var (IntSlotPin.Inputs n) (F circomPrime))
    (hpresent : Affine inp.present) (hneg : Affine inp.negative) (hlen : Affine inp.len)
    (hsp : Affine inp.slot.present) (hsn : Affine inp.slot.negative)
    (hsl : Affine inp.slot.len) (hdigits : AffineW inp.slot.digits) :
    IsR1CSCirc (assertion (IntSlotPin.circuit n) inp) :=
  IsR1CSCirc.assertion (r1cs_intSlotPin n inp hpresent hneg hlen hsp hsn hsl hdigits)

theorem costIs_boolSlotPin (inp : Var BoolSlotPin.Inputs (F circomPrime)) :
    CostIs (BoolSlotPin.main inp) boolSlotPinCost := by
  unfold BoolSlotPin.main boolSlotPinCost
  exact CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ => CostIs.assertZero _

theorem costIs_assertion_boolSlotPin (inp : Var BoolSlotPin.Inputs (F circomPrime)) :
    CostIs (assertion BoolSlotPin.circuit inp) boolSlotPinCost :=
  CostIs.assertion (costIs_boolSlotPin inp)

theorem usesIR_boolSlotPin (inp : Var BoolSlotPin.Inputs (F circomPrime)) :
    UsesIRCirc (BoolSlotPin.main inp) := by
  unfold BoolSlotPin.main
  exact UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ => UsesIRCirc.assertZero _

theorem usesIR_assertion_boolSlotPin (inp : Var BoolSlotPin.Inputs (F circomPrime)) :
    UsesIRCirc (assertion BoolSlotPin.circuit inp) :=
  UsesIRCirc.assertion (usesIR_boolSlotPin inp)

theorem r1cs_boolSlotPin (inp : Var BoolSlotPin.Inputs (F circomPrime))
    (hpresent : Affine inp.present) (hvalue : Affine inp.value)
    (hsp : Affine inp.slot.present) (hsv : Affine inp.slot.value) :
    IsR1CSCirc (BoolSlotPin.main inp) := by
  unfold BoolSlotPin.main
  exact IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hpresent
    (Affine.sub hpresent (Affine.const 1)))) fun _ =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub hsp hpresent))) fun _ =>
    IsR1CSCirc.assertZero (isR1CSRow_of_affine (Affine.sub hsv hvalue))

theorem r1cs_assertion_boolSlotPin (inp : Var BoolSlotPin.Inputs (F circomPrime))
    (hpresent : Affine inp.present) (hvalue : Affine inp.value)
    (hsp : Affine inp.slot.present) (hsv : Affine inp.slot.value) :
    IsR1CSCirc (assertion BoolSlotPin.circuit inp) :=
  IsR1CSCirc.assertion (r1cs_boolSlotPin inp hpresent hvalue hsp hsv)

/-! ## Structural walkers

The remaining gadgets are long `do`-blocks of subcircuit calls and single rows. Their
three certificates all have the same shape — mirror the block with `bind`, close each
leaf with the corresponding per-gadget lemma — so the walk is scripted once here. The
cost walker leaves the total `Count` as a metavariable that the chain instantiates to a
sum of literals; `CostIs.of_eq` then checks it against the named count by arithmetic. -/

theorem CostIs.of_eq {α : Type} {c : Circuit (F circomPrime) α} {K K' : Count}
    (h : CostIs c K) (he : K = K') : CostIs c K' := he ▸ h

/-- Affineness of an expression built from constants, symbolic input cells and
witness / subcircuit output variables. -/
syntax "affine_tac" : tactic
macro_rules
  | `(tactic| affine_tac) =>
    `(tactic| repeat' first
        | assumption
        | exact Affine.zero
        | exact Affine.const _
        | exact Affine.var _
        | apply Affine.add
        | apply Affine.sub
        | apply Affine.neg
        | apply Affine.fconst_mul
        | apply Affine.mul_fconst)

/-! ## Byte classifier

30 single-byte `IsEqual` tests (`⟨2,2⟩` each), one 8-bit decomposition (`⟨8,9⟩`) and
40 witnessed products (`⟨1,1⟩` each). -/

def byteClassCost : Count := ⟨108, 109⟩

set_option maxHeartbeats 1000000 in
theorem costIs_byteClass (x : Var field (F circomPrime)) :
    CostIs (ByteClass.main x) byteClassCost := by
  unfold ByteClass.main
  exact CostIs.of_eq (
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_sub_isEqual _) fun _ =>
  CostIs.bind (costIs_assertion_num2Bits _ _ _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => CostIs.pure _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => CostIs.pure _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => CostIs.pure _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => CostIs.pure _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => CostIs.pure _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (costIs_sub_mul _) fun _ =>
  CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
  CostIs.pure _) (by rfl)

set_option maxHeartbeats 1000000 in
theorem usesIR_byteClass (x : Var field (F circomPrime)) :
    UsesIRCirc (ByteClass.main x) := by
  unfold ByteClass.main
  exact
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
  UsesIRCirc.bind (usesIR_assertion_num2Bits _ _ _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => UsesIRCirc.pure _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => UsesIRCirc.pure _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => UsesIRCirc.pure _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => UsesIRCirc.pure _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => UsesIRCirc.pure _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
  UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) fun _ =>
  UsesIRCirc.pure _

theorem costIs_sub_byteClass (x : Var field (F circomPrime)) :
    CostIs (subcircuit ByteClass.circuit x) byteClassCost :=
  CostIs.subcircuit (costIs_byteClass x)

theorem usesIR_sub_byteClass (x : Var field (F circomPrime)) :
    UsesIRCirc (subcircuit ByteClass.circuit x) :=
  UsesIRCirc.subcircuit (usesIR_byteClass x)


/-! ## Binder-carrying `bind` lemmas

`IsR1CSCirc.bind_out` substitutes the bound value's *definition* into the rest of the
block, so a long straight-line gadget ends up unifying against deeper and deeper terms.
The three lemmas below instead hand the continuation an opaque value together with the
affineness fact the rows need, which keeps every unification linear in the block. -/

theorem IsR1CSCirc.bindA {β : Type}
    {f : Circuit (F circomPrime) (Expression (F circomPrime))}
    {g : Expression (F circomPrime) → Circuit (F circomPrime) β}
    (hf : IsR1CSCirc f) (hfout : ∀ n, Affine (f.output n))
    (hg : ∀ a, Affine a → IsR1CSCirc (g a)) : IsR1CSCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, Lemmas.operationsIsR1CS_append]
  exact ⟨hf n, hg _ (hfout n) (n + f.localLength n)⟩

theorem IsR1CSCirc.bindW {β : Type} {m : ℕ}
    {f : Circuit (F circomPrime) (Var (fields m) (F circomPrime))}
    {g : Var (fields m) (F circomPrime) → Circuit (F circomPrime) β}
    (hf : IsR1CSCirc f) (hfout : ∀ n, AffineW (f.output n))
    (hg : ∀ a, AffineW a → IsR1CSCirc (g a)) : IsR1CSCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, Lemmas.operationsIsR1CS_append]
  exact ⟨hf n, hg _ (hfout n) (n + f.localLength n)⟩

/-- The general form: the continuation is handed an opaque value together with an
arbitrary fact `P` about it. Keeping the bound value opaque is what stops a long
straight-line gadget from re-`whnf`-ing its predecessors' definitions at every step. -/
theorem IsR1CSCirc.bindOf {α β : Type} {f : Circuit (F circomPrime) α}
    {g : α → Circuit (F circomPrime) β} (P : α → Prop)
    (hf : IsR1CSCirc f) (hfout : ∀ n, P (f.output n))
    (hg : ∀ a, P a → IsR1CSCirc (g a)) : IsR1CSCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, Lemmas.operationsIsR1CS_append]
  exact ⟨hf n, hg _ (hfout n) (n + f.localLength n)⟩

theorem IsR1CSCirc.bindP {β : Type} {M : TypeMap} [ProvableType M]
    {f : Circuit (F circomPrime) (Var M (F circomPrime))}
    {g : Var M (F circomPrime) → Circuit (F circomPrime) β}
    (hf : IsR1CSCirc f) (hfout : ∀ n, AffineProvable (f.output n))
    (hg : ∀ a, AffineProvable a → IsR1CSCirc (g a)) : IsR1CSCirc (f >>= g) := by
  intro n
  rw [Circuit.bind_operations_eq, Lemmas.operationsIsR1CS_append]
  exact ⟨hf n, hg _ (hfout n) (n + f.localLength n)⟩

/-- Read one affine cell out of an affine vector. The index and its bound are
**explicit** and meant to be filled in by unification with the goal: `omega` cannot
prove `i < Model.nClaims`, because a named constant is an opaque atom to it. -/
theorem affine_getElem {m : ℕ} {v : Var (fields m) (F circomPrime)} (h : AffineW v)
    (i : ℕ) (hi : i < m) : Affine (v[i]'hi) := h i hi

theorem affine_getElem_fin {m : ℕ} {v : Var (fields m) (F circomPrime)} (h : AffineW v)
    (i : Fin m) : Affine v[i] := h i.val i.isLt

theorem affineW_assertion_num2Bits_output (n : ℕ) (hn : 2 ^ n < circomPrime)
    (x : Var field (F circomPrime)) (off : ℕ) :
    AffineW ((subcircuitWithAssertion (Num2Bits.circuit n hn) x).output off) := by
  show AffineW (varFromOffset (fields n) off : Var (fields n) (F circomPrime))
  exact affineW_varFromOffset n off

/-- Affineness of an expression built from constants, symbolic input cells and
the (affine) values a straight-line block has already bound. The gadget-output
leaves are deliberately **not** here: `affine_sub_lessThan_output` has to `whnf` a
`LessThan.circuit ?n ?hn` whose bit width is still a metavariable, and on a goal it
cannot close that costs minutes. They live in `affine_out`, which only ever runs on a
goal that really is a gadget's output block. -/
syntax "affine_tacW" : tactic
macro_rules
  | `(tactic| affine_tacW) =>
    `(tactic| repeat' first
        | assumption
        | exact Affine.zero
        | exact Affine.const _
        | (refine affine_getElem ?_ _ _ <;> assumption)
        | (refine affine_getElem_fin ?_ _ <;> assumption)
        | apply Affine.add
        | apply Affine.sub
        | apply Affine.neg
        | refine Affine.mul_deg0 ?_ rfl
        | refine Affine.deg0_mul rfl ?_
        | apply Affine.fconst_mul
        | apply Affine.mul_fconst
        | exact Affine.var _)

/-- The `hfout` side of a binder-carrying bind: reduce the block's output through
`bind`/`pure` and then read off its affineness. -/
syntax "affine_out" : tactic
macro_rules
  | `(tactic| affine_out) =>
    `(tactic| (try simp only [Circuit.bind_output_eq, Circuit.pure_output_eq]);
              repeat' first
        | assumption
        | exact Affine.zero
        | exact Affine.const _
        | (refine affine_getElem ?_ _ _ <;> assumption)
        | (refine affine_getElem_fin ?_ _ <;> assumption)
        | apply Affine.add
        | apply Affine.sub
        | apply Affine.neg
        | refine Affine.mul_deg0 ?_ rfl
        | refine Affine.deg0_mul rfl ?_
        | apply Affine.fconst_mul
        | apply Affine.mul_fconst
        | exact affine_sub_mul_output _ _
        | exact affine_sub_isEqual_output _ _
        | exact affine_sub_isZero_output _ _
        | exact affine_sub_lessThan_output _ _ _ _
        | exact Affine.var _)

set_option maxHeartbeats 4000000 in
theorem r1cs_byteClass (x : Var field (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (ByteClass.main x) := by
  unfold ByteClass.main
  exact
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_isEqual _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindW (r1cs_assertion_num2Bits _ _ _ (by affine_tacW))
    (affineW_assertion_num2Bits_output _ _ _) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => IsR1CSCirc.pure _) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => IsR1CSCirc.pure _) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => IsR1CSCirc.pure _) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => IsR1CSCirc.pure _) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => IsR1CSCirc.pure _) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.bindA (IsR1CSCirc.bindA (r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ => r1cs_sub_mul _ (by affine_tacW) (by affine_tacW)) (fun _ => by affine_out) fun _ _ =>
  IsR1CSCirc.pure _

theorem r1cs_sub_byteClass (x : Var field (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (subcircuit ByteClass.circuit x) :=
  IsR1CSCirc.subcircuit (r1cs_byteClass x hx)


/-! ## More affineness leaves -/

theorem IsR1CSCirc.mapVec {α β : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit (F circomPrime) β} {constant : Circuit.ConstantLength body}
    (h : ∀ a n, operationsIsR1CS ((body a).operations n)) :
    IsR1CSCirc (Circuit.map xs body constant) :=
  IsR1CSCirc.mapVec_mem fun i => h xs[i.val]

/-! ## The string sub-automaton -/

def subAutomatonCost : Count := ⟨49, 76⟩

theorem costIs_subAutomaton (inp : Var SubAutomaton.Inputs (F circomPrime)) :
    CostIs (SubAutomaton.main inp) subAutomatonCost := by
  unfold SubAutomaton.main
  exact CostIs.of_eq (
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.mapVec fun _ => costIs_sub_mul _) fun _ =>
    CostIs.forEach fun _ =>
      CostIs.bind (costIs_sub_mul _) fun _ =>
      CostIs.bind (costIs_sub_mul _) fun _ =>
      CostIs.assertZero _) (by rfl)

theorem costIs_assertion_subAutomaton (inp : Var SubAutomaton.Inputs (F circomPrime)) :
    CostIs (assertion SubAutomaton.circuit inp) subAutomatonCost :=
  CostIs.assertion (costIs_subAutomaton inp)

theorem usesIR_subAutomaton (inp : Var SubAutomaton.Inputs (F circomPrime)) :
    UsesIRCirc (SubAutomaton.main inp) := by
  unfold SubAutomaton.main
  exact UsesIRCirc.bind (UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.mapVec fun _ k => usesIR_sub_mul _ k) fun _ =>
    UsesIRCirc.forEach fun _ k =>
      (UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
       UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
       UsesIRCirc.assertZero _) k

theorem usesIR_assertion_subAutomaton (inp : Var SubAutomaton.Inputs (F circomPrime)) :
    UsesIRCirc (assertion SubAutomaton.circuit inp) :=
  UsesIRCirc.assertion (usesIR_subAutomaton inp)

/-- The transition mass entering one sub-state is an affine sum of the edge products. -/
theorem affine_mass {prods : Vector SubAutomaton.E 23} (h : AffineW prods) (j : ℕ) :
    Affine (SubAutomaton.mass prods j) := by
  unfold SubAutomaton.mass
  refine affine_finFoldl' _ 0 Affine.zero fun _acc e hacc => ?_
  split
  · exact Affine.add hacc (affine_getElem_fin h e)
  · exact hacc

theorem r1cs_subAutomaton (inp : Var SubAutomaton.Inputs (F circomPrime))
    (hinStr : Affine inp.inStr) (hactive : Affine inp.active)
    (hcls : ∀ c, Affine (SubAutomaton.clsExpr inp.cls c))
    (hprev : AffineW inp.subPrev) (hnext : AffineW inp.subNext) :
    IsR1CSCirc (SubAutomaton.main inp) := by
  unfold SubAutomaton.main
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_mul (affine_getElem_fin hprev i)
      (Affine.sub (affine_getElem_fin hprev i) (Affine.const 1))) k
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
    (Affine.sub (affine_finFoldl' _ 0 Affine.zero
      (fun acc i h => Affine.add h (affine_getElem_fin hprev i))) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bindW (IsR1CSCirc.mapVec fun e k =>
      r1cs_sub_mul _ (affine_getElem_fin hprev _) (hcls _) k)
    (fun n => affineW_map_output _ _ _ (fun _ _ => affine_sub_mul_output _ _) n)
    fun prods hprods => ?_
  refine IsR1CSCirc.forEach_mem fun j k => ?_
  simp only [Vector.getElem_finRange]
  exact (IsR1CSCirc.bindA (r1cs_sub_mul _ hinStr (affine_mass hprods _))
      (fun _ => by affine_out) fun gated hgated =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hactive
        (Affine.sub (by split <;> [exact Affine.add hgated (Affine.sub (Affine.const 1) hinStr);
                                   exact hgated]) (affine_getElem_fin hprev j)))
      (fun _ => by affine_out) fun d hd =>
    IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub (Affine.sub (affine_getElem_fin hnext j) (affine_getElem_fin hprev j)) hd))) k

theorem r1cs_assertion_subAutomaton (inp : Var SubAutomaton.Inputs (F circomPrime))
    (hinStr : Affine inp.inStr) (hactive : Affine inp.active)
    (hcls : ∀ c, Affine (SubAutomaton.clsExpr inp.cls c))
    (hprev : AffineW inp.subPrev) (hnext : AffineW inp.subNext) :
    IsR1CSCirc (assertion SubAutomaton.circuit inp) :=
  IsR1CSCirc.assertion (r1cs_subAutomaton inp hinStr hactive hcls hprev hnext)


/-! ## Affine folds -/

theorem affine_finFoldl_sum {m : ℕ} {v : Var (fields m) (F circomPrime)} (h : AffineW v) :
    Affine (Fin.foldl m (fun acc t => acc + v[t]) 0) :=
  affine_finFoldl' _ 0 Affine.zero fun _acc t hacc =>
    Affine.add hacc (affine_getElem_fin h t)

theorem affine_finFoldl_scaled {m : ℕ} {v : Var (fields m) (F circomPrime)} (h : AffineW v)
    (c : Fin m → F circomPrime) :
    Affine (Fin.foldl m (fun acc t => acc + v[t] * (c t : Expression (F circomPrime))) 0) :=
  affine_finFoldl' _ 0 Affine.zero fun _acc t hacc =>
    Affine.add hacc (Affine.mul_deg0 (affine_getElem_fin h t) (degree_const _))

/-! ## The main automaton -/

def mainAutomatonCost : Count := ⟨99, 154⟩

theorem costIs_mainAutomaton (inp : Var MainAutomaton.Inputs (F circomPrime)) :
    CostIs (MainAutomaton.main inp) mainAutomatonCost := by
  unfold MainAutomaton.main
  exact CostIs.of_eq (
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.mapVec fun _ => costIs_sub_mul _) fun _ =>
    CostIs.bind (CostIs.mapVec fun _ =>
      CostIs.bind (costIs_sub_mul _) fun _ => costIs_sub_mul _) fun _ =>
    CostIs.forEach fun _ =>
      CostIs.bind (costIs_sub_mul _) fun _ => CostIs.assertZero _) (by rfl)

theorem costIs_assertion_mainAutomaton (inp : Var MainAutomaton.Inputs (F circomPrime)) :
    CostIs (assertion MainAutomaton.circuit inp) mainAutomatonCost :=
  CostIs.assertion (costIs_mainAutomaton inp)

theorem usesIR_mainAutomaton (inp : Var MainAutomaton.Inputs (F circomPrime)) :
    UsesIRCirc (MainAutomaton.main inp) := by
  unfold MainAutomaton.main
  exact UsesIRCirc.bind (UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.mapVec fun _ k => usesIR_sub_mul _ k) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.mapVec fun _ k =>
      (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => usesIR_sub_mul _) k) fun _ =>
    UsesIRCirc.forEach fun _ k =>
      (UsesIRCirc.bind (usesIR_sub_mul _) fun _ => UsesIRCirc.assertZero _) k

theorem usesIR_assertion_mainAutomaton (inp : Var MainAutomaton.Inputs (F circomPrime)) :
    UsesIRCirc (assertion MainAutomaton.circuit inp) :=
  UsesIRCirc.assertion (usesIR_mainAutomaton inp)

theorem affine_plainMass {prods : Vector MainAutomaton.E 50} (h : AffineW prods) (j : ℕ) :
    Affine (MainAutomaton.plainMass prods j) := by
  unfold MainAutomaton.plainMass
  refine affine_finFoldl' _ 0 Affine.zero fun _acc e hacc => ?_
  split
  · exact Affine.add hacc (affine_getElem_fin h e)
  · exact hacc

theorem affine_gatedMass {prods : Vector MainAutomaton.E 11} (h : AffineW prods) (j : ℕ) :
    Affine (MainAutomaton.gatedMass prods j) := by
  unfold MainAutomaton.gatedMass
  refine affine_finFoldl' _ 0 Affine.zero fun _acc e hacc => ?_
  split
  · exact Affine.add hacc (affine_getElem_fin h e)
  · exact hacc

theorem r1cs_mainAutomaton (inp : Var MainAutomaton.Inputs (F circomPrime))
    (hactive : Affine inp.active)
    (hcls : ∀ c, Affine (MainAutomaton.clsExpr inp.cls inp.closeQuote c))
    (hgate : ∀ g, Affine (MainAutomaton.gateExpr inp.kinds g))
    (hprev : AffineW inp.stPrev) (hnext : AffineW inp.stNext) :
    IsR1CSCirc (MainAutomaton.main inp) := by
  unfold MainAutomaton.main
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_mul (affine_getElem_fin hprev i)
      (Affine.sub (affine_getElem_fin hprev i) (Affine.const 1))) k
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
    (Affine.sub (affine_finFoldl_sum hprev) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bindW (IsR1CSCirc.mapVec fun e k =>
      r1cs_sub_mul _ (affine_getElem_fin hprev _) (hcls _) k)
    (fun n => affineW_map_output _ _ _ (fun _ _ => affine_sub_mul_output _ _) n)
    fun plainProds hplain => ?_
  refine IsR1CSCirc.bindW (IsR1CSCirc.mapVec fun e k =>
      (IsR1CSCirc.bindA (r1cs_sub_mul _ (affine_getElem_fin hprev _) (hcls _))
        (fun _ => by affine_out) fun p hp => r1cs_sub_mul _ hp (hgate _)) k)
    (fun n => affineW_map_output _ _ _ (fun _ _ => by affine_out) n)
    fun gatedProds hgated => ?_
  refine IsR1CSCirc.forEach_mem fun j k => ?_
  simp only [Vector.getElem_finRange]
  exact (IsR1CSCirc.bindA (r1cs_sub_mul _ hactive
      (Affine.sub (Affine.add (affine_plainMass hplain _) (affine_gatedMass hgated _))
        (affine_getElem_fin hprev j)))
      (fun _ => by affine_out) fun d hd =>
    IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub (Affine.sub (affine_getElem_fin hnext j) (affine_getElem_fin hprev j)) hd))) k

theorem r1cs_assertion_mainAutomaton (inp : Var MainAutomaton.Inputs (F circomPrime))
    (hactive : Affine inp.active)
    (hcls : ∀ c, Affine (MainAutomaton.clsExpr inp.cls inp.closeQuote c))
    (hgate : ∀ g, Affine (MainAutomaton.gateExpr inp.kinds g))
    (hprev : AffineW inp.stPrev) (hnext : AffineW inp.stNext) :
    IsR1CSCirc (assertion MainAutomaton.circuit inp) :=
  IsR1CSCirc.assertion (r1cs_mainAutomaton inp hactive hcls hgate hprev hnext)

/-! ## The key matcher -/

def matcherCost : Count := ⟨8, 9⟩

theorem costIs_matcher (k : Model.Claim) (inp : Var Matcher.Inputs (F circomPrime)) :
    CostIs (Matcher.main k inp) matcherCost := by
  unfold Matcher.main
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_isEqual _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    costIs_sub_mul _) (by rfl)

theorem costIs_sub_matcher (k : Model.Claim) (inp : Var Matcher.Inputs (F circomPrime)) :
    CostIs (subcircuitWithAssertion (Matcher.circuit k) inp) matcherCost :=
  CostIs.subcircuitWithAssertion (costIs_matcher k inp)

theorem usesIR_matcher (k : Model.Claim) (inp : Var Matcher.Inputs (F circomPrime)) :
    UsesIRCirc (Matcher.main k inp) := by
  unfold Matcher.main
  exact UsesIRCirc.bind (usesIR_sub_isEqual _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    usesIR_sub_mul _

theorem usesIR_sub_matcher (k : Model.Claim) (inp : Var Matcher.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuitWithAssertion (Matcher.circuit k) inp) :=
  UsesIRCirc.subcircuitWithAssertion (usesIR_matcher k inp)

theorem r1cs_matcher (k : Model.Claim) (inp : Var Matcher.Inputs (F circomPrime))
    (hcp : Affine inp.cp) (hemit : Affine inp.emit) (hoh : AffineW inp.kIdxOH)
    (hmPrev : Affine inp.mPrev) (hmNext : Affine inp.mNext)
    (hkeyStart : Affine inp.keyStart) (hkeyClose : Affine inp.keyClose)
    (hstKey : Affine inp.stKey) (hactive : Affine inp.active) :
    IsR1CSCirc (Matcher.main k inp) := by
  unfold Matcher.main
  exact
    IsR1CSCirc.bindA (r1cs_sub_isEqual _ hcp
        (affine_finFoldl_scaled hoh fun t => ((Model.nameAt k t.val : ℕ) : F circomPrime)))
      (fun _ => by affine_out) fun eq heq =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hemit (Affine.sub (Affine.const 1) heq))
      (fun _ => by affine_out) fun mismatch hmis =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hmPrev (Affine.sub (Affine.const 1) hmis))
      (fun _ => by affine_out) fun keep hkeep =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hstKey hkeep) (fun _ => by affine_out) fun held hheld =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hactive
        (Affine.sub (Affine.add hkeyStart hheld) hmPrev)) (fun _ => by affine_out) fun d hd =>
    IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
        (Affine.sub (Affine.sub hmNext hmPrev) hd))) fun _ =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hmPrev (affine_getElem_fin hoh _))
      (fun _ => by affine_out) fun atLen hatLen =>
    r1cs_sub_mul _ hkeyClose hatLen

theorem r1cs_sub_matcher (k : Model.Claim) (inp : Var Matcher.Inputs (F circomPrime))
    (hcp : Affine inp.cp) (hemit : Affine inp.emit) (hoh : AffineW inp.kIdxOH)
    (hmPrev : Affine inp.mPrev) (hmNext : Affine inp.mNext)
    (hkeyStart : Affine inp.keyStart) (hkeyClose : Affine inp.keyClose)
    (hstKey : Affine inp.stKey) (hactive : Affine inp.active) :
    IsR1CSCirc (subcircuitWithAssertion (Matcher.circuit k) inp) :=
  IsR1CSCirc.subcircuitWithAssertion
    (r1cs_matcher k inp hcp hemit hoh hmPrev hmNext hkeyStart hkeyClose hstKey hactive)

theorem affine_sub_matcher_output (k : Model.Claim) (inp : Var Matcher.Inputs (F circomPrime))
    (off : ℕ) : Affine ((subcircuitWithAssertion (Matcher.circuit k) inp).output off) := by
  simp only [circuit_norm]
  affine_tac

/-! ## Routing into one output slot -/

def routeSlotCost (n : ℕ) : Count := ⟨n + 2, n + 2⟩

theorem costIs_routeSlot (n : ℕ) [NeZero n] (hn : n ≤ Model.ofsMax)
    (inp : Var (RouteSlot.Inputs n) (F circomPrime)) :
    CostIs (RouteSlot.main n hn inp) (routeSlotCost n) := by
  unfold RouteSlot.main
  exact CostIs.of_eq (
    CostIs.bind (CostIs.mapVec fun _ => costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.pure _)
    (Count.ext' (by simp only [routeSlotCost, mulCost, Count.zero, Count.add_allocations]; omega)
      (by simp only [routeSlotCost, mulCost, Count.zero, Count.add_constraints]; omega))

theorem costIs_sub_routeSlot (n : ℕ) [NeZero n] (hn : n ≤ Model.ofsMax)
    (inp : Var (RouteSlot.Inputs n) (F circomPrime)) :
    CostIs (subcircuit (RouteSlot.circuit n hn) inp) (routeSlotCost n) :=
  CostIs.subcircuit (costIs_routeSlot n hn inp)

theorem usesIR_routeSlot (n : ℕ) [NeZero n] (hn : n ≤ Model.ofsMax)
    (inp : Var (RouteSlot.Inputs n) (F circomPrime)) :
    UsesIRCirc (RouteSlot.main n hn inp) := by
  unfold RouteSlot.main
  exact UsesIRCirc.bind (UsesIRCirc.mapVec fun _ k => usesIR_sub_mul _ k) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_routeSlot (n : ℕ) [NeZero n] (hn : n ≤ Model.ofsMax)
    (inp : Var (RouteSlot.Inputs n) (F circomPrime)) :
    UsesIRCirc (subcircuit (RouteSlot.circuit n hn) inp) :=
  UsesIRCirc.subcircuit (usesIR_routeSlot n hn inp)

theorem affine_ofsSum (n : ℕ) (hn : n ≤ Model.ofsMax)
    {v : Vector (Expression (F circomPrime)) Model.ofsMax} (h : AffineW v) :
    Affine (Fin.foldl n (fun acc t => acc + RouteSlot.ofsAt hn v t) 0) :=
  affine_finFoldl' _ 0 Affine.zero fun _acc t hacc =>
    Affine.add hacc (h t.val (lt_of_lt_of_le t.isLt hn))

theorem r1cs_routeSlot (n : ℕ) [NeZero n] (hn : n ≤ Model.ofsMax)
    (inp : Var (RouteSlot.Inputs n) (F circomPrime))
    (hflag : Affine inp.claimFlag) (hoh : AffineW inp.ofsOH) (hcells : AffineW inp.cells) :
    IsR1CSCirc (RouteSlot.main n hn inp) := by
  unfold RouteSlot.main
  refine IsR1CSCirc.bindW (IsR1CSCirc.mapVec_mem fun t k => ?_)
    (fun m => affineW_map_output _ _ _ (fun _ _ => affine_sub_mul_output _ _) m)
    fun prods hprods => ?_
  · simp only [Vector.getElem_finRange]
    exact r1cs_sub_mul _ (hoh _ (lt_of_lt_of_le t.isLt hn)) (affine_getElem_fin hcells t) k
  exact
    IsR1CSCirc.bindA (r1cs_sub_mul _ hflag (affine_finFoldl_sum hprods))
      (fun _ => by affine_out) fun sel hsel =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hflag (affine_ofsSum n hn hoh))
      (fun _ => by affine_out) fun ex hex =>
    IsR1CSCirc.pure _

theorem r1cs_sub_routeSlot (n : ℕ) [NeZero n] (hn : n ≤ Model.ofsMax)
    (inp : Var (RouteSlot.Inputs n) (F circomPrime))
    (hflag : Affine inp.claimFlag) (hoh : AffineW inp.ofsOH) (hcells : AffineW inp.cells) :
    IsR1CSCirc (subcircuit (RouteSlot.circuit n hn) inp) :=
  IsR1CSCirc.subcircuit (r1cs_routeSlot n hn inp hflag hoh hcells)


theorem affineW_mapFinRange_output {m : ℕ} [NeZero m]
    (body : Fin m → Circuit (F circomPrime) (Expression (F circomPrime)))
    (constant : Circuit.ConstantLength body)
    (h : ∀ i n, Affine ((body i).output n)) (n : ℕ) :
    AffineW ((Circuit.mapFinRange m body constant).output n) := by
  intro i hi
  rw [Circuit.mapFinRange.output_eq, Vector.getElem_mapFinRange]
  exact h _ _


/-! ## Affine blocks of the structured gadget outputs

A gadget that returns a *structure* cannot hand its caller a single `Affine` fact, and
reading a field out of `varFromOffset` costs a `whnf` of the whole provable-type
instance. Both bundles below are therefore established once, against the gadget's
output block, and then carried through the caller's block as opaque hypotheses. -/

/-- The flags of a byte-class block that `Step` and the two automata read. -/
structure AffineCls (c : ByteClass.Outputs (Expression (F circomPrime))) : Prop where
  sub : ∀ sc, Affine (SubAutomaton.clsExpr c sc)
  main : ∀ cq cl, Affine cq → Affine (MainAutomaton.clsExpr c cq cl)
  isQuote : Affine c.bytes.isQuote
  isBackslash : Affine c.bytes.isBackslash
  isSlash : Affine c.bytes.isSlash
  isLowerB : Affine c.bytes.isLowerB
  isLowerF : Affine c.bytes.isLowerF
  isLowerN : Affine c.bytes.isLowerN
  isLowerR : Affine c.bytes.isLowerR
  isLowerT : Affine c.bytes.isLowerT
  isMinus : Affine c.bytes.isMinus
  isLowerE : Affine c.bytes.isLowerE
  isUnescaped : Affine c.classes.isUnescaped
  isSimpleEsc : Affine c.classes.isSimpleEsc
  isHex : Affine c.classes.isHex
  isCont : Affine c.classes.isCont
  isDigit : Affine c.classes.isDigit
  isUpperHex : Affine c.classes.isUpperHex
  isLowerHex : Affine c.classes.isLowerHex

set_option maxHeartbeats 4000000 in
theorem affineCls_sub_byteClass_output (x : Var field (F circomPrime)) (off : ℕ) :
    AffineCls ((subcircuit ByteClass.circuit x).output off) := by
  simp only [circuit_norm]
  refine ⟨fun sc => ?_, fun cq cl hcq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases sc <;> affine_tac
  · cases cl <;> affine_tac
  all_goals affine_tac

/-- The two signals one `RouteSlot` returns. -/
structure AffineRoute (o : RouteSlot.Outputs (Expression (F circomPrime))) : Prop where
  sel : Affine o.sel
  ex : Affine o.exists_

theorem affineRoute_sub_routeSlot_output (n : ℕ) [NeZero n] (hn : n ≤ Model.ofsMax)
    (inp : Var (RouteSlot.Inputs n) (F circomPrime)) (off : ℕ) :
    AffineRoute ((subcircuit (RouteSlot.circuit n hn) inp).output off) := by
  simp only [circuit_norm]
  exact ⟨by affine_tac, by affine_tac⟩



/-! ## The gadgets of one position

Each of the ten gadgets `Step` is glued out of gets the same three certificates as
the older ones: the exact operation count, the witness-IR property and the R1CS
shape, plus the affineness of its outputs as a bundle (a gadget that returns a
structure cannot hand its caller a single `Affine` fact). -/

/-! ### The claim register's shape -/

def claimKindsCost : Count := ⟨0, 23⟩

theorem costIs_claimKinds (inp : Var ClaimKinds.Inputs (F circomPrime)) :
    CostIs (ClaimKinds.main inp) claimKindsCost := by
  unfold ClaimKinds.main
  exact CostIs.of_eq (
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.assertZero _) (by rfl)

theorem costIs_assertion_claimKinds (inp : Var ClaimKinds.Inputs (F circomPrime)) :
    CostIs (assertion ClaimKinds.circuit inp) claimKindsCost :=
  CostIs.assertion (costIs_claimKinds inp)

theorem usesIR_claimKinds (inp : Var ClaimKinds.Inputs (F circomPrime)) :
    UsesIRCirc (ClaimKinds.main inp) := by
  unfold ClaimKinds.main
  exact UsesIRCirc.bind (UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.forEach fun _ k => UsesIRCirc.assertZero _ k) fun _ =>
    UsesIRCirc.assertZero _

theorem usesIR_assertion_claimKinds (inp : Var ClaimKinds.Inputs (F circomPrime)) :
    UsesIRCirc (assertion ClaimKinds.circuit inp) :=
  UsesIRCirc.assertion (usesIR_claimKinds inp)

theorem affine_kStrE {cl : Vector (Expression (F circomPrime)) Model.nClaims} (h : AffineW cl) :
    Affine (ClaimKinds.kStrE cl) := by
  unfold ClaimKinds.kStrE; affine_tacW

theorem affine_kIntE {cl : Vector (Expression (F circomPrime)) Model.nClaims} (h : AffineW cl) :
    Affine (ClaimKinds.kIntE cl) := by
  unfold ClaimKinds.kIntE; affine_tacW

theorem affine_kBoolE {cl : Vector (Expression (F circomPrime)) Model.nClaims} (h : AffineW cl) :
    Affine (ClaimKinds.kBoolE cl) := by
  unfold ClaimKinds.kBoolE; affine_tacW

theorem affine_kUnkE {cl : Vector (Expression (F circomPrime)) Model.nClaims} (h : AffineW cl) :
    Affine (ClaimKinds.kUnkE cl) := by
  unfold ClaimKinds.kUnkE
  exact Affine.sub (Affine.sub (Affine.sub (Affine.const 1) (affine_kStrE h))
    (affine_kIntE h)) (affine_kBoolE h)

theorem r1cs_claimKinds (inp : Var ClaimKinds.Inputs (F circomPrime))
    (hcl : AffineW inp.claimPrev) (hm : AffineW inp.mPrev) :
    IsR1CSCirc (ClaimKinds.main inp) := by
  unfold ClaimKinds.main
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_mul (affine_getElem_fin hcl i)
      (Affine.sub (affine_getElem_fin hcl i) (Affine.const 1))) k
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach_mem fun i k => ?_) fun _ => ?_
  · simp only [Vector.getElem_finRange]
    exact IsR1CSCirc.assertZero (isR1CSRow_mul (affine_getElem_fin hm i)
      (Affine.sub (affine_getElem_fin hm i) (Affine.const 1))) k
  exact IsR1CSCirc.assertZero (isR1CSRow_mul (affine_kUnkE hcl)
    (Affine.sub (affine_kUnkE hcl) (Affine.const 1)))

theorem r1cs_assertion_claimKinds (inp : Var ClaimKinds.Inputs (F circomPrime))
    (hcl : AffineW inp.claimPrev) (hm : AffineW inp.mPrev) :
    IsR1CSCirc (assertion ClaimKinds.circuit inp) :=
  IsR1CSCirc.assertion (r1cs_claimKinds inp hcl hm)

/-! ### The emission flags -/

def emitCost : Count := ⟨8, 8⟩

theorem costIs_emit (inp : Var Emit.Inputs (F circomPrime)) :
    CostIs (Emit.main inp) emitCost := by
  unfold Emit.main Rows.mul
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.pure _) (by rfl)

theorem costIs_sub_emit (inp : Var Emit.Inputs (F circomPrime)) :
    CostIs (subcircuit Emit.circuit inp) emitCost :=
  CostIs.subcircuit (costIs_emit inp)

theorem usesIR_emit (inp : Var Emit.Inputs (F circomPrime)) :
    UsesIRCirc (Emit.main inp) := by
  unfold Emit.main Rows.mul
  exact UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_emit (inp : Var Emit.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuit Emit.circuit inp) :=
  UsesIRCirc.subcircuit (usesIR_emit inp)

theorem r1cs_emit (inp : Var Emit.Inputs (F circomPrime))
    (hinStr : Affine inp.inStr) (hsub : AffineW inp.subPrev)
    (hun : Affine inp.isUnescaped) (hse : Affine inp.isSimpleEsc)
    (hhex : Affine inp.isHex) (hcont : Affine inp.isCont) :
    IsR1CSCirc (Emit.main inp) := by
  unfold Emit.main Rows.mul
  exact
    IsR1CSCirc.bindA (r1cs_sub_mul _ hinStr (affine_getElem hsub _ (by decide)))
      (fun _ => by affine_out) fun inPlain hinPlain =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hinStr (affine_getElem hsub _ (by decide)))
      (fun _ => by affine_out) fun inEsc hinEsc =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hinStr (affine_getElem hsub _ (by decide)))
      (fun _ => by affine_out) fun inH4 hinH4 =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hinStr (affine_getElem hsub _ (by decide)))
      (fun _ => by affine_out) fun inC1 hinC1 =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hinPlain hun) (fun _ => by affine_out) fun _ _ =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hinEsc hse) (fun _ => by affine_out) fun _ _ =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hinH4 hhex) (fun _ => by affine_out) fun _ _ =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hinC1 hcont) (fun _ => by affine_out) fun _ _ =>
    IsR1CSCirc.pure _

theorem r1cs_sub_emit (inp : Var Emit.Inputs (F circomPrime))
    (hinStr : Affine inp.inStr) (hsub : AffineW inp.subPrev)
    (hun : Affine inp.isUnescaped) (hse : Affine inp.isSimpleEsc)
    (hhex : Affine inp.isHex) (hcont : Affine inp.isCont) :
    IsR1CSCirc (subcircuit Emit.circuit inp) :=
  IsR1CSCirc.subcircuit (r1cs_emit inp hinStr hsub hun hse hhex hcont)

/-- The four flags an `Emit` block returns. -/
structure AffineEmit (o : Emit.Outputs (Expression (F circomPrime))) : Prop where
  emitPlain : Affine o.emitPlain
  emitEsc : Affine o.emitEsc
  emitU : Affine o.emitU
  emitUtf8 : Affine o.emitUtf8

theorem affineEmit_sub_emit_output (inp : Var Emit.Inputs (F circomPrime)) (off : ℕ) :
    AffineEmit ((subcircuit Emit.circuit inp).output off) := by
  simp only [circuit_norm]
  exact ⟨by affine_tac, by affine_tac, by affine_tac, by affine_tac⟩

/-! ### The decoded code point -/

def codePointCost : Count := ⟨8, 9⟩

theorem costIs_codePoint (inp : Var CodePoint.Inputs (F circomPrime)) :
    CostIs (CodePoint.main inp) codePointCost := by
  unfold CodePoint.main Rows.mul Rows.freeze
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => CostIs.assertZero _) fun _ =>
    CostIs.pure _) (by rfl)

theorem costIs_sub_codePoint (inp : Var CodePoint.Inputs (F circomPrime)) :
    CostIs (subcircuitWithAssertion CodePoint.circuit inp) codePointCost :=
  CostIs.subcircuitWithAssertion (costIs_codePoint inp)

theorem usesIR_codePoint (inp : Var CodePoint.Inputs (F circomPrime)) :
    UsesIRCirc (CodePoint.main inp) := by
  unfold CodePoint.main Rows.mul Rows.freeze
  exact UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
      UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_codePoint (inp : Var CodePoint.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuitWithAssertion CodePoint.circuit inp) :=
  UsesIRCirc.subcircuitWithAssertion (usesIR_codePoint inp)

theorem r1cs_codePoint (inp : Var CodePoint.Inputs (F circomPrime))
    (hbyte : Affine inp.byte) (hdig : Affine inp.isDigit) (hup : Affine inp.isUpperHex)
    (hlo : Affine inp.isLowerHex) (hesc : Affine inp.escVal)
    (hep : Affine inp.emitPlain) (hee : Affine inp.emitEsc) (heu : Affine inp.emitU)
    (he8 : Affine inp.emitUtf8) (hinH : Affine inp.inH)
    (hhexPrev : Affine inp.hexAccPrev) (hhexNext : Affine inp.hexAccNext)
    (hactive : Affine inp.active) :
    IsR1CSCirc (CodePoint.main inp) := by
  unfold CodePoint.main Rows.mul Rows.freeze
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hdig (by affine_tacW))
    (fun _ => by affine_out) fun _ hd => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hup (by affine_tacW))
    (fun _ => by affine_out) fun _ hu => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hlo (by affine_tacW))
    (fun _ => by affine_out) fun _ hl => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hep hbyte)
    (fun _ => by affine_out) fun _ _ => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hee hesc)
    (fun _ => by affine_out) fun _ _ => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ heu (by affine_tacW))
    (fun _ => by affine_out) fun _ _ => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hinH (by affine_tacW))
    (fun _ => by affine_out) fun _ hnew => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.bindA (r1cs_sub_mul _ hactive (Affine.sub hnew hhexPrev))
    (fun _ => by affine_out) fun _ hdd =>
    IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub (Affine.sub hhexNext hhexPrev) hdd))) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem r1cs_sub_codePoint (inp : Var CodePoint.Inputs (F circomPrime))
    (hbyte : Affine inp.byte) (hdig : Affine inp.isDigit) (hup : Affine inp.isUpperHex)
    (hlo : Affine inp.isLowerHex) (hesc : Affine inp.escVal)
    (hep : Affine inp.emitPlain) (hee : Affine inp.emitEsc) (heu : Affine inp.emitU)
    (he8 : Affine inp.emitUtf8) (hinH : Affine inp.inH)
    (hhexPrev : Affine inp.hexAccPrev) (hhexNext : Affine inp.hexAccNext)
    (hactive : Affine inp.active) :
    IsR1CSCirc (subcircuitWithAssertion CodePoint.circuit inp) :=
  IsR1CSCirc.subcircuitWithAssertion (r1cs_codePoint inp hbyte hdig hup hlo hesc hep hee heu
    he8 hinH hhexPrev hhexNext hactive)

theorem affine_sub_codePoint_output (inp : Var CodePoint.Inputs (F circomPrime))
    (he8 : Affine inp.emitUtf8) (off : ℕ) :
    Affine ((subcircuitWithAssertion CodePoint.circuit inp).output off).cp := by
  simp only [circuit_norm]
  affine_tac

/-! ### The key index -/

def keyIndexCost : Count := ⟨21, 24⟩

theorem costIs_keyIndex (inp : Var KeyIndex.Inputs (F circomPrime)) :
    CostIs (KeyIndex.main inp) keyIndexCost := by
  unfold KeyIndex.main Rows.mul Rows.freeze
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_oneHot _ _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => CostIs.assertZero _) fun _ =>
    CostIs.pure _) (by rfl)

theorem costIs_sub_keyIndex (inp : Var KeyIndex.Inputs (F circomPrime)) :
    CostIs (subcircuitWithAssertion KeyIndex.circuit inp) keyIndexCost :=
  CostIs.subcircuitWithAssertion (costIs_keyIndex inp)

theorem usesIR_keyIndex (inp : Var KeyIndex.Inputs (F circomPrime)) :
    UsesIRCirc (KeyIndex.main inp) := by
  unfold KeyIndex.main Rows.mul Rows.freeze
  exact UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_oneHot _ _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
      UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_keyIndex (inp : Var KeyIndex.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuitWithAssertion KeyIndex.circuit inp) :=
  UsesIRCirc.subcircuitWithAssertion (usesIR_keyIndex inp)

theorem r1cs_keyIndex (inp : Var KeyIndex.Inputs (F circomPrime))
    (hkp : Affine inp.stKeyPrev) (hkn : Affine inp.stKeyNext) (hcq : Affine inp.closeQuote)
    (hemit : Affine inp.emit) (hprev : Affine inp.kIdxPrev) (hnext : Affine inp.kIdxNext)
    (hactive : Affine inp.active) :
    IsR1CSCirc (KeyIndex.main inp) := by
  unfold KeyIndex.main Rows.mul Rows.freeze
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hkn (Affine.sub (Affine.const 1) hkp))
    (fun _ => by affine_out) fun _ _ => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hkp hcq) (fun _ => by affine_out) fun _ _ => ?_
  refine IsR1CSCirc.bindW (r1cs_sub_oneHot _ _ hprev)
    (fun n => affineW_sub_oneHot_output _ _ n) fun oh hoh => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hemit
    (Affine.sub (Affine.const 1) (affine_getElem hoh _ (by decide))))
    (fun _ => by affine_out) fun _ hinc => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hkp (Affine.add hprev hinc))
    (fun _ => by affine_out) fun _ hnew => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.bindA (r1cs_sub_mul _ hactive (Affine.sub hnew hprev))
    (fun _ => by affine_out) fun _ hd =>
    IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub (Affine.sub hnext hprev) hd))) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem r1cs_sub_keyIndex (inp : Var KeyIndex.Inputs (F circomPrime))
    (hkp : Affine inp.stKeyPrev) (hkn : Affine inp.stKeyNext) (hcq : Affine inp.closeQuote)
    (hemit : Affine inp.emit) (hprev : Affine inp.kIdxPrev) (hnext : Affine inp.kIdxNext)
    (hactive : Affine inp.active) :
    IsR1CSCirc (subcircuitWithAssertion KeyIndex.circuit inp) :=
  IsR1CSCirc.subcircuitWithAssertion
    (r1cs_keyIndex inp hkp hkn hcq hemit hprev hnext hactive)

/-- What a `KeyIndex` block returns. -/
structure AffineKeyIndex (o : KeyIndex.Outputs (Expression (F circomPrime))) : Prop where
  keyStart : Affine o.keyStart
  keyClose : Affine o.keyClose
  kIdxOH : AffineW o.kIdxOH

theorem affineKeyIndex_sub_keyIndex_output (inp : Var KeyIndex.Inputs (F circomPrime))
    (off : ℕ) : AffineKeyIndex ((subcircuitWithAssertion KeyIndex.circuit inp).output off) :=
  ⟨by dsimp only [circuit_norm]; affine_tac, by dsimp only [circuit_norm]; affine_tac,
   affineW_varFromOffset Model.kIdxMax (off + 1 + 1)⟩

/-! ### The key matchers -/

def keyMatchersCost : Count := ⟨88, 99⟩

theorem costIs_keyMatchers (inp : Var KeyMatchers.Inputs (F circomPrime)) :
    CostIs (KeyMatchers.main inp) keyMatchersCost := by
  unfold KeyMatchers.main
  exact CostIs.of_eq (
    CostIs.bind (CostIs.mapFinRange fun _ => costIs_sub_matcher _ _) fun _ =>
    CostIs.pure _) (by rfl)

theorem costIs_sub_keyMatchers (inp : Var KeyMatchers.Inputs (F circomPrime)) :
    CostIs (subcircuitWithAssertion KeyMatchers.circuit inp) keyMatchersCost :=
  CostIs.subcircuitWithAssertion (costIs_keyMatchers inp)

theorem usesIR_keyMatchers (inp : Var KeyMatchers.Inputs (F circomPrime)) :
    UsesIRCirc (KeyMatchers.main inp) := by
  unfold KeyMatchers.main
  exact UsesIRCirc.bind (UsesIRCirc.mapFinRange fun _ k => usesIR_sub_matcher _ _ k) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_keyMatchers (inp : Var KeyMatchers.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuitWithAssertion KeyMatchers.circuit inp) :=
  UsesIRCirc.subcircuitWithAssertion (usesIR_keyMatchers inp)

theorem r1cs_keyMatchers (inp : Var KeyMatchers.Inputs (F circomPrime))
    (hcp : Affine inp.cp) (hemit : Affine inp.emit) (hoh : AffineW inp.kIdxOH)
    (hmP : AffineW inp.mPrev) (hmN : AffineW inp.mNext)
    (hks : Affine inp.keyStart) (hkc : Affine inp.keyClose)
    (hstKey : Affine inp.stKey) (hactive : Affine inp.active) :
    IsR1CSCirc (KeyMatchers.main inp) := by
  unfold KeyMatchers.main
  exact IsR1CSCirc.bind (IsR1CSCirc.mapFinRange fun kc k =>
      r1cs_sub_matcher kc _ hcp hemit hoh (affine_getElem_fin hmP kc)
        (affine_getElem_fin hmN kc) hks hkc hstKey hactive k) fun _ =>
    IsR1CSCirc.pure _

theorem r1cs_sub_keyMatchers (inp : Var KeyMatchers.Inputs (F circomPrime))
    (hcp : Affine inp.cp) (hemit : Affine inp.emit) (hoh : AffineW inp.kIdxOH)
    (hmP : AffineW inp.mPrev) (hmN : AffineW inp.mNext)
    (hks : Affine inp.keyStart) (hkc : Affine inp.keyClose)
    (hstKey : Affine inp.stKey) (hactive : Affine inp.active) :
    IsR1CSCirc (subcircuitWithAssertion KeyMatchers.circuit inp) :=
  IsR1CSCirc.subcircuitWithAssertion
    (r1cs_keyMatchers inp hcp hemit hoh hmP hmN hks hkc hstKey hactive)

theorem affineW_sub_keyMatchers_output (inp : Var KeyMatchers.Inputs (F circomPrime))
    (off : ℕ) :
    AffineW ((subcircuitWithAssertion KeyMatchers.circuit inp).output off).match_ := by
  intro i hi
  show Affine (Vector.mapFinRange Model.nClaims
    (fun k : Fin Model.nClaims => (var ⟨off + k.val * 8 + 7⟩ : Expression (F circomPrime))))[i]
  rw [Vector.getElem_mapFinRange]
  affine_tac

/-! ### The claim register -/

def claimRegCost : Count := ⟨22, 33⟩

theorem costIs_claimReg (inp : Var ClaimReg.Inputs (F circomPrime)) :
    CostIs (ClaimReg.main inp) claimRegCost := by
  unfold ClaimReg.main Rows.mul Rows.freeze
  exact CostIs.of_eq (
    CostIs.forEach fun _ =>
      CostIs.bind (costIs_sub_mul _) fun _ =>
      CostIs.bind (costIs_sub_mul _) fun _ =>
      CostIs.assertZero _) (by rfl)

theorem costIs_assertion_claimReg (inp : Var ClaimReg.Inputs (F circomPrime)) :
    CostIs (assertion ClaimReg.circuit inp) claimRegCost :=
  CostIs.assertion (costIs_claimReg inp)

theorem usesIR_claimReg (inp : Var ClaimReg.Inputs (F circomPrime)) :
    UsesIRCirc (ClaimReg.main inp) := by
  unfold ClaimReg.main Rows.mul Rows.freeze
  exact UsesIRCirc.forEach fun _ k =>
    (UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
     UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
     UsesIRCirc.assertZero _) k

theorem usesIR_assertion_claimReg (inp : Var ClaimReg.Inputs (F circomPrime)) :
    UsesIRCirc (assertion ClaimReg.circuit inp) :=
  UsesIRCirc.assertion (usesIR_claimReg inp)

theorem r1cs_claimReg (inp : Var ClaimReg.Inputs (F circomPrime))
    (hactive : Affine inp.active) (hkc : Affine inp.keyClose) (hks : Affine inp.keyStart)
    (hmatch : AffineW inp.match_) (hcP : AffineW inp.claimPrev) (hcN : AffineW inp.claimNext) :
    IsR1CSCirc (ClaimReg.main inp) := by
  unfold ClaimReg.main Rows.mul Rows.freeze
  refine IsR1CSCirc.forEach_mem fun kc k => ?_
  simp only [Vector.getElem_finRange]
  exact (IsR1CSCirc.bindA (r1cs_sub_mul _
      (Affine.sub (Affine.sub (Affine.const 1) hkc) hks) (affine_getElem_fin hcP kc))
      (fun _ => by affine_out) fun _ hkept =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hactive (Affine.sub
        (Affine.add (affine_getElem_fin hmatch kc) hkept) (affine_getElem_fin hcP kc)))
      (fun _ => by affine_out) fun _ hd =>
    IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub (Affine.sub (affine_getElem_fin hcN kc) (affine_getElem_fin hcP kc)) hd))) k

theorem r1cs_assertion_claimReg (inp : Var ClaimReg.Inputs (F circomPrime))
    (hactive : Affine inp.active) (hkc : Affine inp.keyClose) (hks : Affine inp.keyStart)
    (hmatch : AffineW inp.match_) (hcP : AffineW inp.claimPrev) (hcN : AffineW inp.claimNext) :
    IsR1CSCirc (assertion ClaimReg.circuit inp) :=
  IsR1CSCirc.assertion (r1cs_claimReg inp hactive hkc hks hmatch hcP hcN)

/-! ### The value characters -/

def valueEmitCost : Count := ⟨5, 5⟩

theorem costIs_valueEmit (inp : Var ValueEmit.Inputs (F circomPrime)) :
    CostIs (ValueEmit.main inp) valueEmitCost := by
  unfold ValueEmit.main Rows.mul
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.pure _) (by rfl)

theorem costIs_sub_valueEmit (inp : Var ValueEmit.Inputs (F circomPrime)) :
    CostIs (subcircuit ValueEmit.circuit inp) valueEmitCost :=
  CostIs.subcircuit (costIs_valueEmit inp)

theorem usesIR_valueEmit (inp : Var ValueEmit.Inputs (F circomPrime)) :
    UsesIRCirc (ValueEmit.main inp) := by
  unfold ValueEmit.main Rows.mul
  exact UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_valueEmit (inp : Var ValueEmit.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuit ValueEmit.circuit inp) :=
  UsesIRCirc.subcircuit (usesIR_valueEmit inp)

theorem r1cs_valueEmit (inp : Var ValueEmit.Inputs (F circomPrime))
    (hemit : Affine inp.emit) (hstr : Affine inp.stStr) (hdig : Affine inp.isDigit)
    (hnum : Affine inp.stNum) (hk : Affine inp.kStrInt) (hcp : Affine inp.cp)
    (hbyte : Affine inp.byte) :
    IsR1CSCirc (ValueEmit.main inp) := by
  unfold ValueEmit.main Rows.mul
  exact
    IsR1CSCirc.bindA (r1cs_sub_mul _ hemit hstr) (fun _ => by affine_out) fun _ hse =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hdig hnum) (fun _ => by affine_out) fun _ hde =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ (Affine.add hse hde) hk)
      (fun _ => by affine_out) fun _ _ =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hse hcp) (fun _ => by affine_out) fun _ _ =>
    IsR1CSCirc.bindA (r1cs_sub_mul _ hde (Affine.sub hbyte (Affine.const _)))
      (fun _ => by affine_out) fun _ _ =>
    IsR1CSCirc.pure _

theorem r1cs_sub_valueEmit (inp : Var ValueEmit.Inputs (F circomPrime))
    (hemit : Affine inp.emit) (hstr : Affine inp.stStr) (hdig : Affine inp.isDigit)
    (hnum : Affine inp.stNum) (hk : Affine inp.kStrInt) (hcp : Affine inp.cp)
    (hbyte : Affine inp.byte) :
    IsR1CSCirc (subcircuit ValueEmit.circuit inp) :=
  IsR1CSCirc.subcircuit (r1cs_valueEmit inp hemit hstr hdig hnum hk hcp hbyte)

/-- What a `ValueEmit` block returns. -/
structure AffineValueEmit (o : ValueEmit.Outputs (Expression (F circomPrime))) : Prop where
  strEmit : Affine o.strEmit
  digitEmit : Affine o.digitEmit
  write : Affine o.write
  valOut : Affine o.valOut

theorem affineValueEmit_sub_valueEmit_output (inp : Var ValueEmit.Inputs (F circomPrime))
    (off : ℕ) : AffineValueEmit ((subcircuit ValueEmit.circuit inp).output off) := by
  simp only [circuit_norm]
  exact ⟨by affine_tac, by affine_tac, by affine_tac, by affine_tac⟩

/-! ### The value offset -/

def offsetCost : Count := ⟨132, 135⟩

theorem costIs_offset (inp : Var Offset.Inputs (F circomPrime)) :
    CostIs (Offset.main inp) offsetCost := by
  unfold Offset.main Rows.mul Rows.freeze
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_oneHot _ _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (CostIs.bind (costIs_sub_mul _) fun _ => CostIs.assertZero _) fun _ =>
    CostIs.pure _) (by rfl)

theorem costIs_sub_offset (inp : Var Offset.Inputs (F circomPrime)) :
    CostIs (subcircuitWithAssertion Offset.circuit inp) offsetCost :=
  CostIs.subcircuitWithAssertion (costIs_offset inp)

theorem usesIR_offset (inp : Var Offset.Inputs (F circomPrime)) :
    UsesIRCirc (Offset.main inp) := by
  unfold Offset.main Rows.mul Rows.freeze
  exact UsesIRCirc.bind (usesIR_sub_oneHot _ _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
      UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_offset (inp : Var Offset.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuitWithAssertion Offset.circuit inp) :=
  UsesIRCirc.subcircuitWithAssertion (usesIR_offset inp)

theorem r1cs_offset (inp : Var Offset.Inputs (F circomPrime))
    (hprev : Affine inp.ofsPrev) (hnext : Affine inp.ofsNext) (hvEmit : Affine inp.vEmit)
    (hinVal : Affine inp.inVal) (hactive : Affine inp.active) :
    IsR1CSCirc (Offset.main inp) := by
  unfold Offset.main Rows.mul Rows.freeze
  refine IsR1CSCirc.bindW (r1cs_sub_oneHot _ _ hprev)
    (fun n => affineW_sub_oneHot_output _ _ n) fun oh hoh => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hvEmit
    (Affine.sub (Affine.const 1) (affine_getElem hoh _ (by decide))))
    (fun _ => by affine_out) fun _ hinc => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hinVal hprev)
    (fun _ => by affine_out) fun _ hkept => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.bindA
    (r1cs_sub_mul _ hactive (Affine.sub (Affine.add hkept hinc) hprev))
    (fun _ => by affine_out) fun _ hd =>
    IsR1CSCirc.assertZero (isR1CSRow_of_affine
      (Affine.sub (Affine.sub hnext hprev) hd))) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem r1cs_sub_offset (inp : Var Offset.Inputs (F circomPrime))
    (hprev : Affine inp.ofsPrev) (hnext : Affine inp.ofsNext) (hvEmit : Affine inp.vEmit)
    (hinVal : Affine inp.inVal) (hactive : Affine inp.active) :
    IsR1CSCirc (subcircuitWithAssertion Offset.circuit inp) :=
  IsR1CSCirc.subcircuitWithAssertion (r1cs_offset inp hprev hnext hvEmit hinVal hactive)

theorem affineW_sub_offset_output (inp : Var Offset.Inputs (F circomPrime)) (off : ℕ) :
    AffineW ((subcircuitWithAssertion Offset.circuit inp).output off).ofsOH :=
  affineW_varFromOffset Model.ofsMax off

/-! ### The per-position signals -/

def claimSignalsCost : Count := ⟨25, 26⟩

theorem costIs_claimSignals (inp : Var ClaimSignals.Inputs (F circomPrime)) :
    CostIs (ClaimSignals.main inp) claimSignalsCost := by
  unfold ClaimSignals.main Rows.mul
  exact CostIs.of_eq (
    CostIs.bind (CostIs.mapFinRange fun _ => costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (CostIs.mapFinRange fun _ => costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.pure _) (by rfl)

theorem costIs_sub_claimSignals (inp : Var ClaimSignals.Inputs (F circomPrime)) :
    CostIs (subcircuitWithAssertion ClaimSignals.circuit inp) claimSignalsCost :=
  CostIs.subcircuitWithAssertion (costIs_claimSignals inp)

theorem usesIR_claimSignals (inp : Var ClaimSignals.Inputs (F circomPrime)) :
    UsesIRCirc (ClaimSignals.main inp) := by
  unfold ClaimSignals.main Rows.mul
  exact UsesIRCirc.bind (UsesIRCirc.mapFinRange fun _ k => usesIR_sub_mul _ k) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.mapFinRange fun _ k => usesIR_sub_mul _ k) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_claimSignals (inp : Var ClaimSignals.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuitWithAssertion ClaimSignals.circuit inp) :=
  UsesIRCirc.subcircuitWithAssertion (usesIR_claimSignals inp)

theorem r1cs_claimSignals (inp : Var ClaimSignals.Inputs (F circomPrime))
    (hvEmit : Affine inp.vEmit) (hcl : AffineW inp.claimPrev) (hpval : Affine inp.stPval)
    (hminus : Affine inp.isMinus) (ht3 : Affine inp.stT3) (hlowerE : Affine inp.isLowerE)
    (hnMemPrev : Affine inp.nMemPrev) (hnMemNext : Affine inp.nMemNext)
    (hks : Affine inp.keyStart) :
    IsR1CSCirc (ClaimSignals.main inp) := by
  unfold ClaimSignals.main Rows.mul
  refine IsR1CSCirc.bind (IsR1CSCirc.mapFinRange fun kc k =>
    r1cs_sub_mul _ hvEmit (affine_getElem_fin hcl kc) k) fun _ => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hpval hminus)
    (fun _ => by affine_out) fun _ hmf => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.mapFinRange fun kc k =>
    r1cs_sub_mul _ hmf (affine_getElem_fin hcl kc) k) fun _ => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ ht3 hlowerE)
    (fun _ => by affine_out) fun _ htd => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ htd (affine_getElem hcl 6 (by decide)))
    (fun _ => by affine_out) fun _ _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine
    (Affine.sub (Affine.sub hnMemNext hnMemPrev) hks))) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem r1cs_sub_claimSignals (inp : Var ClaimSignals.Inputs (F circomPrime))
    (hvEmit : Affine inp.vEmit) (hcl : AffineW inp.claimPrev) (hpval : Affine inp.stPval)
    (hminus : Affine inp.isMinus) (ht3 : Affine inp.stT3) (hlowerE : Affine inp.isLowerE)
    (hnMemPrev : Affine inp.nMemPrev) (hnMemNext : Affine inp.nMemNext)
    (hks : Affine inp.keyStart) :
    IsR1CSCirc (subcircuitWithAssertion ClaimSignals.circuit inp) :=
  IsR1CSCirc.subcircuitWithAssertion (r1cs_claimSignals inp hvEmit hcl hpval hminus ht3
    hlowerE hnMemPrev hnMemNext hks)

/-- What a `ClaimSignals` block returns. -/
structure AffineSignals (o : ClaimSignals.Outputs (Expression (F circomPrime))) : Prop where
  vEmitK : AffineW o.vEmitK
  minusK : AffineW o.minusK
  trueK : Affine o.trueK

theorem affineSignals_sub_claimSignals_output (inp : Var ClaimSignals.Inputs (F circomPrime))
    (off : ℕ) :
    AffineSignals ((subcircuitWithAssertion ClaimSignals.circuit inp).output off) :=
  ⟨by intro i hi
      rw [show (subcircuitWithAssertion ClaimSignals.circuit inp).output off
            = ClaimSignals.circuit.output inp off from rfl, ClaimSignals.out_vEmitK,
          Vector.getElem_mapFinRange]
      affine_tac,
   by intro i hi
      rw [show (subcircuitWithAssertion ClaimSignals.circuit inp).output off
            = ClaimSignals.circuit.output inp off from rfl, ClaimSignals.out_minusK,
          Vector.getElem_mapFinRange]
      affine_tac,
   by dsimp only [circuit_norm]; affine_tac⟩

/-! ### Routing -/

def routeHalfCost (n0 n1 n2 n3 n4 : ℕ) : Count :=
  ⟨n0 + 2 + (n1 + 2 + (n2 + 2 + (n3 + 2 + (n4 + 2)))),
   n0 + 2 + (n1 + 2 + (n2 + 2 + (n3 + 2 + (n4 + 2))))⟩

theorem costIs_routeHalf {n0 n1 n2 n3 n4 : ℕ} [NeZero n0] [NeZero n1] [NeZero n2] [NeZero n3]
    [NeZero n4] (h0 : n0 ≤ Model.ofsMax) (h1 : n1 ≤ Model.ofsMax) (h2 : n2 ≤ Model.ofsMax)
    (h3 : n3 ≤ Model.ofsMax) (h4 : n4 ≤ Model.ofsMax)
    (inp : Var (RouteHalf.Inputs n0 n1 n2 n3 n4) (F circomPrime)) :
    CostIs (RouteHalf.main h0 h1 h2 h3 h4 inp) (routeHalfCost n0 n1 n2 n3 n4) := by
  unfold RouteHalf.main
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_routeSlot _ _ _) fun _ =>
    CostIs.bind (costIs_sub_routeSlot _ _ _) fun _ =>
    CostIs.bind (costIs_sub_routeSlot _ _ _) fun _ =>
    CostIs.bind (costIs_sub_routeSlot _ _ _) fun _ =>
    CostIs.bind (costIs_sub_routeSlot _ _ _) fun _ =>
    CostIs.pure _) (by rfl)

theorem costIs_sub_routeHalf {n0 n1 n2 n3 n4 : ℕ} [NeZero n0] [NeZero n1] [NeZero n2]
    [NeZero n3] [NeZero n4] (h0 : n0 ≤ Model.ofsMax) (h1 : n1 ≤ Model.ofsMax)
    (h2 : n2 ≤ Model.ofsMax) (h3 : n3 ≤ Model.ofsMax) (h4 : n4 ≤ Model.ofsMax)
    (inp : Var (RouteHalf.Inputs n0 n1 n2 n3 n4) (F circomPrime)) :
    CostIs (subcircuit (RouteHalf.circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4) inp)
      (routeHalfCost n0 n1 n2 n3 n4) :=
  CostIs.subcircuit (costIs_routeHalf h0 h1 h2 h3 h4 inp)

theorem usesIR_routeHalf {n0 n1 n2 n3 n4 : ℕ} [NeZero n0] [NeZero n1] [NeZero n2] [NeZero n3]
    [NeZero n4] (h0 : n0 ≤ Model.ofsMax) (h1 : n1 ≤ Model.ofsMax) (h2 : n2 ≤ Model.ofsMax)
    (h3 : n3 ≤ Model.ofsMax) (h4 : n4 ≤ Model.ofsMax)
    (inp : Var (RouteHalf.Inputs n0 n1 n2 n3 n4) (F circomPrime)) :
    UsesIRCirc (RouteHalf.main h0 h1 h2 h3 h4 inp) := by
  unfold RouteHalf.main
  exact UsesIRCirc.bind (usesIR_sub_routeSlot _ _ _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_routeSlot _ _ _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_routeSlot _ _ _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_routeSlot _ _ _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_routeSlot _ _ _) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_routeHalf {n0 n1 n2 n3 n4 : ℕ} [NeZero n0] [NeZero n1] [NeZero n2]
    [NeZero n3] [NeZero n4] (h0 : n0 ≤ Model.ofsMax) (h1 : n1 ≤ Model.ofsMax)
    (h2 : n2 ≤ Model.ofsMax) (h3 : n3 ≤ Model.ofsMax) (h4 : n4 ≤ Model.ofsMax)
    (inp : Var (RouteHalf.Inputs n0 n1 n2 n3 n4) (F circomPrime)) :
    UsesIRCirc (subcircuit (RouteHalf.circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4) inp) :=
  UsesIRCirc.subcircuit (usesIR_routeHalf h0 h1 h2 h3 h4 inp)

theorem r1cs_routeHalf {n0 n1 n2 n3 n4 : ℕ} [NeZero n0] [NeZero n1] [NeZero n2] [NeZero n3]
    [NeZero n4] (h0 : n0 ≤ Model.ofsMax) (h1 : n1 ≤ Model.ofsMax) (h2 : n2 ≤ Model.ofsMax)
    (h3 : n3 ≤ Model.ofsMax) (h4 : n4 ≤ Model.ofsMax)
    (inp : Var (RouteHalf.Inputs n0 n1 n2 n3 n4) (F circomPrime))
    (c0 : Affine inp.claim0) (c1 : Affine inp.claim1) (c2 : Affine inp.claim2)
    (c3 : Affine inp.claim3) (c4 : Affine inp.claim4) (hoh : AffineW inp.ofsOH)
    (e0 : AffineW inp.cells0) (e1 : AffineW inp.cells1) (e2 : AffineW inp.cells2)
    (e3 : AffineW inp.cells3) (e4 : AffineW inp.cells4) :
    IsR1CSCirc (RouteHalf.main h0 h1 h2 h3 h4 inp) := by
  unfold RouteHalf.main
  exact
    IsR1CSCirc.bindOf AffineRoute (r1cs_sub_routeSlot _ _ _ c0 hoh e0)
      (fun n => affineRoute_sub_routeSlot_output _ _ _ n) fun _ hr0 =>
    IsR1CSCirc.bindOf AffineRoute (r1cs_sub_routeSlot _ _ _ c1 hoh e1)
      (fun n => affineRoute_sub_routeSlot_output _ _ _ n) fun _ hr1 =>
    IsR1CSCirc.bindOf AffineRoute (r1cs_sub_routeSlot _ _ _ c2 hoh e2)
      (fun n => affineRoute_sub_routeSlot_output _ _ _ n) fun _ hr2 =>
    IsR1CSCirc.bindOf AffineRoute (r1cs_sub_routeSlot _ _ _ c3 hoh e3)
      (fun n => affineRoute_sub_routeSlot_output _ _ _ n) fun _ hr3 =>
    IsR1CSCirc.bindOf AffineRoute (r1cs_sub_routeSlot _ _ _ c4 hoh e4)
      (fun n => affineRoute_sub_routeSlot_output _ _ _ n) fun _ hr4 =>
    IsR1CSCirc.pure _

theorem r1cs_sub_routeHalf {n0 n1 n2 n3 n4 : ℕ} [NeZero n0] [NeZero n1] [NeZero n2]
    [NeZero n3] [NeZero n4] (h0 : n0 ≤ Model.ofsMax) (h1 : n1 ≤ Model.ofsMax)
    (h2 : n2 ≤ Model.ofsMax) (h3 : n3 ≤ Model.ofsMax) (h4 : n4 ≤ Model.ofsMax)
    (inp : Var (RouteHalf.Inputs n0 n1 n2 n3 n4) (F circomPrime))
    (c0 : Affine inp.claim0) (c1 : Affine inp.claim1) (c2 : Affine inp.claim2)
    (c3 : Affine inp.claim3) (c4 : Affine inp.claim4) (hoh : AffineW inp.ofsOH)
    (e0 : AffineW inp.cells0) (e1 : AffineW inp.cells1) (e2 : AffineW inp.cells2)
    (e3 : AffineW inp.cells3) (e4 : AffineW inp.cells4) :
    IsR1CSCirc (subcircuit (RouteHalf.circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4) inp) :=
  IsR1CSCirc.subcircuit (r1cs_routeHalf h0 h1 h2 h3 h4 inp c0 c1 c2 c3 c4 hoh e0 e1 e2 e3 e4)

/-- The two signals a `RouteHalf` block returns. -/
structure AffineHalf (o : RouteHalf.Outputs (Expression (F circomPrime))) : Prop where
  sel : Affine o.sel
  ex : Affine o.exists_

theorem affineHalf_sub_routeHalf_output {n0 n1 n2 n3 n4 : ℕ} [NeZero n0] [NeZero n1]
    [NeZero n2] [NeZero n3] [NeZero n4] (h0 : n0 ≤ Model.ofsMax) (h1 : n1 ≤ Model.ofsMax)
    (h2 : n2 ≤ Model.ofsMax) (h3 : n3 ≤ Model.ofsMax) (h4 : n4 ≤ Model.ofsMax)
    (inp : Var (RouteHalf.Inputs n0 n1 n2 n3 n4) (F circomPrime)) (off : ℕ) :
    AffineHalf ((subcircuit (RouteHalf.circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4) inp).output off) := by
  simp only [circuit_norm]
  exact ⟨by affine_tac, by affine_tac⟩

def routeCellsCost : Count := ⟨684, 686⟩

theorem costIs_routeCells (inp : Var RouteCells.Inputs (F circomPrime)) :
    CostIs (RouteCells.main inp) routeCellsCost := by
  unfold RouteCells.main
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_routeHalf _ _ _ _ _ _) fun _ =>
    CostIs.bind (costIs_sub_routeHalf _ _ _ _ _ _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.assertZero _) (by rfl)

theorem costIs_assertion_routeCells (inp : Var RouteCells.Inputs (F circomPrime)) :
    CostIs (assertion RouteCells.circuit inp) routeCellsCost :=
  CostIs.assertion (costIs_routeCells inp)

theorem usesIR_routeCells (inp : Var RouteCells.Inputs (F circomPrime)) :
    UsesIRCirc (RouteCells.main inp) := by
  unfold RouteCells.main
  exact UsesIRCirc.bind (usesIR_sub_routeHalf _ _ _ _ _ _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_routeHalf _ _ _ _ _ _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.assertZero _

theorem usesIR_assertion_routeCells (inp : Var RouteCells.Inputs (F circomPrime)) :
    UsesIRCirc (assertion RouteCells.circuit inp) :=
  UsesIRCirc.assertion (usesIR_routeCells inp)

theorem r1cs_routeCells (inp : Var RouteCells.Inputs (F circomPrime))
    (hwrite : Affine inp.write) (hvalOut : Affine inp.valOut)
    (hcl : AffineW inp.claimPrev) (hoh : AffineW inp.ofsOH)
    (hiss : AffineW inp.iss) (hsub : AffineW inp.sub) (haud : AffineW inp.aud)
    (hazp : AffineW inp.azp) (hhd : AffineW inp.hd) (hemail : AffineW inp.email)
    (hnonce : AffineW inp.nonce) (hatHash : AffineW inp.atHash) (hiat : AffineW inp.iat)
    (hexp : AffineW inp.exp) :
    IsR1CSCirc (RouteCells.main inp) := by
  unfold RouteCells.main
  refine IsR1CSCirc.bindOf AffineHalf
    (r1cs_sub_routeHalf _ _ _ _ _ _ (affine_getElem hcl 0 (by decide))
      (affine_getElem hcl 1 (by decide)) (affine_getElem hcl 2 (by decide))
      (affine_getElem hcl 3 (by decide)) (affine_getElem hcl 4 (by decide))
      hoh hiss hsub haud hazp hhd)
    (fun n => affineHalf_sub_routeHalf_output _ _ _ _ _ _ n) fun a ha => ?_
  refine IsR1CSCirc.bindOf AffineHalf
    (r1cs_sub_routeHalf _ _ _ _ _ _ (affine_getElem hcl 5 (by decide))
      (affine_getElem hcl 7 (by decide)) (affine_getElem hcl 8 (by decide))
      (affine_getElem hcl 9 (by decide)) (affine_getElem hcl 10 (by decide))
      hoh hemail hnonce hatHash hiat hexp)
    (fun n => affineHalf_sub_routeHalf_output _ _ _ _ _ _ n) fun b hb => ?_
  obtain ⟨hsa, hxa⟩ := ha
  obtain ⟨hsb, hxb⟩ := hb
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_mul hwrite
    (Affine.sub (Affine.add hsa hsb) hvalOut))) fun _ => ?_
  exact IsR1CSCirc.assertZero (isR1CSRow_mul hwrite
    (Affine.sub (Affine.add hxa hxb) (Affine.const 1)))

theorem r1cs_assertion_routeCells (inp : Var RouteCells.Inputs (F circomPrime))
    (hwrite : Affine inp.write) (hvalOut : Affine inp.valOut)
    (hcl : AffineW inp.claimPrev) (hoh : AffineW inp.ofsOH)
    (hiss : AffineW inp.iss) (hsub : AffineW inp.sub) (haud : AffineW inp.aud)
    (hazp : AffineW inp.azp) (hhd : AffineW inp.hd) (hemail : AffineW inp.email)
    (hnonce : AffineW inp.nonce) (hatHash : AffineW inp.atHash) (hiat : AffineW inp.iat)
    (hexp : AffineW inp.exp) :
    IsR1CSCirc (assertion RouteCells.circuit inp) :=
  IsR1CSCirc.assertion (r1cs_routeCells inp hwrite hvalOut hcl hoh hiss hsub haud hazp hhd
    hemail hnonce hatHash hiat hexp)

/-! ### The ASCII check -/

def asciiCheckCost : Count := ⟨19, 21⟩

theorem costIs_asciiCheck (inp : Var AsciiCheck.Inputs (F circomPrime)) :
    CostIs (AsciiCheck.main inp) asciiCheckCost := by
  unfold AsciiCheck.main Rows.mul
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_lessThan _ _ _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.assertZero _) (by rfl)

theorem costIs_assertion_asciiCheck (inp : Var AsciiCheck.Inputs (F circomPrime)) :
    CostIs (assertion AsciiCheck.circuit inp) asciiCheckCost :=
  CostIs.assertion (costIs_asciiCheck inp)

theorem usesIR_asciiCheck (inp : Var AsciiCheck.Inputs (F circomPrime)) :
    UsesIRCirc (AsciiCheck.main inp) := by
  unfold AsciiCheck.main Rows.mul
  exact UsesIRCirc.bind (usesIR_sub_lessThan _ _ _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.assertZero _

theorem usesIR_assertion_asciiCheck (inp : Var AsciiCheck.Inputs (F circomPrime)) :
    UsesIRCirc (assertion AsciiCheck.circuit inp) :=
  UsesIRCirc.assertion (usesIR_asciiCheck inp)

theorem r1cs_asciiCheck (inp : Var AsciiCheck.Inputs (F circomPrime))
    (hcp : Affine inp.cp) (hwrite : Affine inp.write) (hstr : Affine inp.stStr) :
    IsR1CSCirc (AsciiCheck.main inp) := by
  unfold AsciiCheck.main Rows.mul
  refine IsR1CSCirc.bindA (r1cs_sub_lessThan _ _ _ hcp (Affine.const _))
    (fun _ => by affine_out) fun _ hlt => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hwrite hstr)
    (fun _ => by affine_out) fun _ hws => ?_
  exact IsR1CSCirc.assertZero (isR1CSRow_mul hws (Affine.sub (Affine.const 1) hlt))

theorem r1cs_assertion_asciiCheck (inp : Var AsciiCheck.Inputs (F circomPrime))
    (hcp : Affine inp.cp) (hwrite : Affine inp.write) (hstr : Affine inp.stStr) :
    IsR1CSCirc (assertion AsciiCheck.circuit inp) :=
  IsR1CSCirc.assertion (r1cs_asciiCheck inp hcp hwrite hstr)


/-! ## One position: the local helpers -/

theorem costIs_freeze (a p nw nx : Expression (F circomPrime)) :
    CostIs (Rows.freeze a p nw nx) ⟨1, 2⟩ := by
  unfold Rows.freeze Rows.mul
  exact CostIs.of_eq (CostIs.bind (costIs_sub_mul _) fun _ => CostIs.assertZero _) (by rfl)

theorem usesIR_freeze (a p nw nx : Expression (F circomPrime)) :
    UsesIRCirc (Rows.freeze a p nw nx) := by
  unfold Rows.freeze Rows.mul
  exact UsesIRCirc.bind (usesIR_sub_mul _) fun _ => UsesIRCirc.assertZero _

theorem r1cs_freeze (a p nw nx : Expression (F circomPrime))
    (ha : Affine a) (hp : Affine p) (hnw : Affine nw) (hnx : Affine nx) :
    IsR1CSCirc (Rows.freeze a p nw nx) := by
  unfold Rows.freeze Rows.mul
  exact IsR1CSCirc.bindA (r1cs_sub_mul _ ha (Affine.sub hnw hp)) (fun _ => by affine_out)
    fun d hd => IsR1CSCirc.assertZero (isR1CSRow_of_affine (Affine.sub (Affine.sub hnx hp) hd))

/-! ## One position -/

def stepCost : Count := ⟨1269, 1410⟩

theorem costIs_step (inp : Var Step.Inputs (F circomPrime)) :
    CostIs (Step.main inp) stepCost := by
  unfold Step.main Rows.mul
  exact CostIs.of_eq (
    CostIs.bind (costIs_sub_byteClass _) fun _ =>
    CostIs.bind (costIs_assertion_claimKinds _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ =>
    CostIs.bind (costIs_sub_mul _) fun _ =>
    CostIs.bind (costIs_assertion_subAutomaton _) fun _ =>
    CostIs.bind (costIs_assertion_mainAutomaton _) fun _ =>
    CostIs.bind (costIs_sub_emit _) fun _ =>
    CostIs.bind (costIs_sub_codePoint _) fun _ =>
    CostIs.bind (costIs_sub_keyIndex _) fun _ =>
    CostIs.bind (costIs_sub_keyMatchers _) fun _ =>
    CostIs.bind (costIs_assertion_claimReg _) fun _ =>
    CostIs.bind (costIs_sub_valueEmit _) fun _ =>
    CostIs.bind (costIs_sub_offset _) fun _ =>
    CostIs.bind (costIs_sub_claimSignals _) fun _ =>
    CostIs.bind (costIs_assertion_routeCells _) fun _ =>
    CostIs.bind (costIs_assertion_asciiCheck _) fun _ =>
    CostIs.pure _) (by rfl)

theorem costIs_sub_step (inp : Var Step.Inputs (F circomPrime)) :
    CostIs (subcircuitWithAssertion Step.circuit inp) stepCost :=
  CostIs.subcircuitWithAssertion (costIs_step inp)

theorem usesIR_step (inp : Var Step.Inputs (F circomPrime)) :
    UsesIRCirc (Step.main inp) := by
  unfold Step.main Rows.mul
  exact
    UsesIRCirc.bind (usesIR_sub_byteClass _) fun _ =>
    UsesIRCirc.bind (usesIR_assertion_claimKinds _) fun _ =>
    UsesIRCirc.bind (UsesIRCirc.assertZero _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_mul _) fun _ =>
    UsesIRCirc.bind (usesIR_assertion_subAutomaton _) fun _ =>
    UsesIRCirc.bind (usesIR_assertion_mainAutomaton _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_emit _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_codePoint _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_keyIndex _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_keyMatchers _) fun _ =>
    UsesIRCirc.bind (usesIR_assertion_claimReg _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_valueEmit _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_offset _) fun _ =>
    UsesIRCirc.bind (usesIR_sub_claimSignals _) fun _ =>
    UsesIRCirc.bind (usesIR_assertion_routeCells _) fun _ =>
    UsesIRCirc.bind (usesIR_assertion_asciiCheck _) fun _ =>
    UsesIRCirc.pure _

theorem usesIR_sub_step (inp : Var Step.Inputs (F circomPrime)) :
    UsesIRCirc (subcircuitWithAssertion Step.circuit inp) :=
  UsesIRCirc.subcircuitWithAssertion (usesIR_step inp)


set_option maxHeartbeats 1000000 in
theorem r1cs_step (inp : Var Step.Inputs (F circomPrime))
    (hbyte : Affine inp.byte) (hlenFlag : Affine inp.lenFlag)
    (haccmPrev : Affine inp.accmPrev) (haccmNext : Affine inp.accmNext)
    (hstPrev : AffineW inp.stPrev) (hstNext : AffineW inp.stNext)
    (hsubPrev : AffineW inp.subPrev) (hsubNext : AffineW inp.subNext)
    (hhexPrev : Affine inp.hexAccPrev) (hhexNext : Affine inp.hexAccNext)
    (hkIdxPrev : Affine inp.kIdxPrev) (hkIdxNext : Affine inp.kIdxNext)
    (hmPrev : AffineW inp.mPrev) (hmNext : AffineW inp.mNext)
    (hclaimPrev : AffineW inp.claimPrev) (hclaimNext : AffineW inp.claimNext)
    (hofsPrev : Affine inp.ofsPrev) (hofsNext : Affine inp.ofsNext)
    (hnMemPrev : Affine inp.nMemPrev) (hnMemNext : Affine inp.nMemNext)
    (hiss : AffineW inp.out.iss.bytes) (hsub : AffineW inp.out.sub.bytes)
    (haud : AffineW inp.out.aud.bytes) (hazp : AffineW inp.out.azp.bytes)
    (hhd : AffineW inp.out.hd.bytes) (hemail : AffineW inp.out.email.bytes)
    (hnonce : AffineW inp.out.nonce.bytes) (hatHash : AffineW inp.out.atHash.bytes)
    (hiat : AffineW inp.out.iat.digits) (hexp : AffineW inp.out.exp.digits) :
    IsR1CSCirc (Step.main inp) := by
  unfold Step.main Rows.mul
  refine IsR1CSCirc.bindOf AffineCls (r1cs_sub_byteClass _ hbyte)
    (fun n => affineCls_sub_byteClass_output _ n) fun c hc => ?_
  obtain ⟨hcSub, hcMain, hcQuote, hcBackslash, hcSlash, hcLowerB, hcLowerF, hcLowerN,
    hcLowerR, hcLowerT, hcMinus, hcLowerE, hcUnescaped, hcSimpleEsc, hcHex, hcCont,
    hcDigit, hcUpperHex, hcLowerHex⟩ := hc
  refine IsR1CSCirc.bind (r1cs_assertion_claimKinds _ hclaimPrev hmPrev) fun _ => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero (isR1CSRow_of_affine (by affine_tacW)))
    fun _ => ?_
  refine IsR1CSCirc.bindA (r1cs_sub_mul _ hcQuote (by affine_tacW))
    (fun _ => by affine_out) fun closeQuote hcloseQuote => ?_
  refine IsR1CSCirc.bind (r1cs_assertion_subAutomaton _ (by affine_tacW) (by affine_tacW)
    hcSub hsubPrev hsubNext) fun _ => ?_
  refine IsR1CSCirc.bind (r1cs_assertion_mainAutomaton _ (by affine_tacW)
    (fun cl => hcMain _ cl hcloseQuote)
    (by
      intro g
      have hS : Affine (ClaimKinds.kStrE inp.claimPrev) := affine_kStrE hclaimPrev
      have hI : Affine (ClaimKinds.kIntE inp.claimPrev) := affine_kIntE hclaimPrev
      have hB : Affine (ClaimKinds.kBoolE inp.claimPrev) := affine_kBoolE hclaimPrev
      have hU : Affine (ClaimKinds.kUnkE inp.claimPrev) := affine_kUnkE hclaimPrev
      cases g <;> affine_tacW) hstPrev hstNext) fun _ => ?_
  refine IsR1CSCirc.bindOf AffineEmit
    (r1cs_sub_emit _ (by affine_tacW) hsubPrev hcUnescaped hcSimpleEsc hcHex hcCont)
    (fun n => affineEmit_sub_emit_output _ n) fun em hem => ?_
  obtain ⟨hEP, hEE, hEU, hE8⟩ := hem
  refine IsR1CSCirc.bindOf (fun o => Affine (CodePoint.Outputs.cp o))
    (r1cs_sub_codePoint _ hbyte hcDigit hcUpperHex hcLowerHex (by affine_tacW)
      hEP hEE hEU hE8 (by affine_tacW) hhexPrev hhexNext (by affine_tacW))
    (fun n => affine_sub_codePoint_output _ hE8 n) fun cpo hcp => ?_
  refine IsR1CSCirc.bindOf AffineKeyIndex
    (r1cs_sub_keyIndex _ (by affine_tacW) (by affine_tacW) hcloseQuote (by affine_tacW)
      hkIdxPrev hkIdxNext (by affine_tacW))
    (fun n => affineKeyIndex_sub_keyIndex_output _ n) fun ki hki => ?_
  obtain ⟨hKS, hKC, hKOH⟩ := hki
  refine IsR1CSCirc.bindOf (fun o => AffineW (KeyMatchers.Outputs.match_ o))
    (r1cs_sub_keyMatchers _ hcp (by affine_tacW) hKOH hmPrev hmNext hKS hKC
      (by affine_tacW) (by affine_tacW))
    (fun n => affineW_sub_keyMatchers_output _ n) fun km hkm => ?_
  refine IsR1CSCirc.bind (r1cs_assertion_claimReg _ (by affine_tacW) hKC hKS hkm
    hclaimPrev hclaimNext) fun _ => ?_
  refine IsR1CSCirc.bindOf AffineValueEmit
    (r1cs_sub_valueEmit _ (by affine_tacW) (by affine_tacW) hcDigit (by affine_tacW)
      (by
        have hS : Affine (ClaimKinds.kStrE inp.claimPrev) := affine_kStrE hclaimPrev
        have hI : Affine (ClaimKinds.kIntE inp.claimPrev) := affine_kIntE hclaimPrev
        affine_tacW) hcp hbyte)
    (fun n => affineValueEmit_sub_valueEmit_output _ n) fun ve hve => ?_
  obtain ⟨hSE, hDE, hW, hVO⟩ := hve
  refine IsR1CSCirc.bindOf (fun o => AffineW (Offset.Outputs.ofsOH o))
    (r1cs_sub_offset _ hofsPrev hofsNext (by affine_tacW) (by affine_tacW) (by affine_tacW))
    (fun n => affineW_sub_offset_output _ n) fun ofs hofs => ?_
  refine IsR1CSCirc.bindOf AffineSignals
    (r1cs_sub_claimSignals _ (by affine_tacW) hclaimPrev (by affine_tacW) hcMinus
      (by affine_tacW) hcLowerE hnMemPrev hnMemNext hKS)
    (fun n => affineSignals_sub_claimSignals_output _ n) fun sig hsig => ?_
  obtain ⟨hVEK, hMK, hTK⟩ := hsig
  refine IsR1CSCirc.bind (r1cs_assertion_routeCells _ hW hVO hclaimPrev hofs
    hiss hsub haud hazp hhd hemail hnonce hatHash hiat hexp) fun _ => ?_
  refine IsR1CSCirc.bind (r1cs_assertion_asciiCheck _ hcp hW (by affine_tacW)) fun _ => ?_
  exact IsR1CSCirc.pure _

theorem r1cs_sub_step (inp : Var Step.Inputs (F circomPrime))
    (hbyte : Affine inp.byte) (hlenFlag : Affine inp.lenFlag)
    (haccmPrev : Affine inp.accmPrev) (haccmNext : Affine inp.accmNext)
    (hstPrev : AffineW inp.stPrev) (hstNext : AffineW inp.stNext)
    (hsubPrev : AffineW inp.subPrev) (hsubNext : AffineW inp.subNext)
    (hhexPrev : Affine inp.hexAccPrev) (hhexNext : Affine inp.hexAccNext)
    (hkIdxPrev : Affine inp.kIdxPrev) (hkIdxNext : Affine inp.kIdxNext)
    (hmPrev : AffineW inp.mPrev) (hmNext : AffineW inp.mNext)
    (hclaimPrev : AffineW inp.claimPrev) (hclaimNext : AffineW inp.claimNext)
    (hofsPrev : Affine inp.ofsPrev) (hofsNext : Affine inp.ofsNext)
    (hnMemPrev : Affine inp.nMemPrev) (hnMemNext : Affine inp.nMemNext)
    (hiss : AffineW inp.out.iss.bytes) (hsub : AffineW inp.out.sub.bytes)
    (haud : AffineW inp.out.aud.bytes) (hazp : AffineW inp.out.azp.bytes)
    (hhd : AffineW inp.out.hd.bytes) (hemail : AffineW inp.out.email.bytes)
    (hnonce : AffineW inp.out.nonce.bytes) (hatHash : AffineW inp.out.atHash.bytes)
    (hiat : AffineW inp.out.iat.digits) (hexp : AffineW inp.out.exp.digits) :
    IsR1CSCirc (subcircuitWithAssertion Step.circuit inp) :=
  IsR1CSCirc.subcircuitWithAssertion (r1cs_step inp hbyte hlenFlag haccmPrev haccmNext hstPrev hstNext
    hsubPrev hsubNext hhexPrev hhexNext hkIdxPrev hkIdxNext hmPrev hmNext hclaimPrev hclaimNext
    hofsPrev hofsNext hnMemPrev hnMemNext hiss hsub haud hazp hhd hemail hnonce hatHash hiat hexp)


/-! ## The top-level blocks

`main` witnesses the whole run in eleven raw witness-IR blocks, slices them per
position, and reads the output slots back out of the output block. The bundles below
turn each of those blocks into the affineness facts its consumers need, once. -/

theorem affineW_input_buffer (input : Var Input (F circomPrime))
    (hinput : AffineProvable input) : AffineW input.buffer := by
  obtain ⟨buf, len⟩ := input
  intro i hi
  have hsz : size Input = bufferLen + 1 := rfl
  have hx := hinput i (by omega)
  simp only [circuit_norm, explicit_provable_type] at hx
  show Affine buf[i]
  rw [Vector.getElem_append_left' hi
    (#v[len] ++ (#v[] : Vector (Expression (F circomPrime)) 0))]
  exact hx

theorem affine_input_len (input : Var Input (F circomPrime))
    (hinput : AffineProvable input) : Affine input.len := by
  obtain ⟨buf, len⟩ := input
  have hsz : size Input = bufferLen + 1 := rfl
  have hx := hinput bufferLen (by omega)
  simp only [circuit_norm, explicit_provable_type] at hx
  show Affine len
  rw [show len = (#v[len] : Vector (Expression (F circomPrime)) 1)[0] from rfl,
    Vector.getElem_append_left' (by omega : (0 : ℕ) < 1)
      (#v[] : Vector (Expression (F circomPrime)) 0),
    Vector.getElem_append_right' buf (by omega : (0 : ℕ) < 1 + 0)]
  exact hx

theorem affineW_witnessIR_output (m : ℕ) (ir : Witgen.WitgenIR (F circomPrime) m) (n : ℕ) :
    AffineW ((witnessIR (fields m) ir).output n) := by
  show AffineW (varFromOffset (fields m) n : Var (fields m) (F circomPrime))
  exact affineW_varFromOffset m n

theorem affineProvable_witnessIR_output {M : TypeMap} [ProvableType M]
    (ir : Witgen.WitgenIR (F circomPrime) (size M)) (n : ℕ) :
    AffineProvable ((witnessIR M ir).output n) := by
  show AffineProvable (varFromOffset M n : Var M (F circomPrime))
  exact affineProvable_varFromOffset n

/-! ### Slicing a position-major register -/

theorem affineW_sliceAt {n : ℕ} {v : Vector (Expression (F circomPrime)) (n * Witness.slots)}
    (h : AffineW v) (i : ℕ) (hi : i < Witness.slots) : AffineW (sliceAt n v i hi) := by
  intro s hs
  rw [sliceAt, Vector.getElem_ofFn]
  exact h _ _

theorem affine_prevAt {v : Vector (Expression (F circomPrime)) Witness.slots}
    (h : AffineW v) (i : Fin bufferLen) : Affine (prevAt v i) := h _ _

theorem affine_nextAt {v : Vector (Expression (F circomPrime)) Witness.slots}
    (h : AffineW v) (i : Fin bufferLen) : Affine (nextAt v i) := h _ _

/-! ### The output slots -/

/-- Affineness of every cell of the circuit's output block. -/
structure AffineSlots (o : Output (Expression (F circomPrime))) : Prop where
  issP : Affine o.iss.present
  issL : Affine o.iss.len
  issB : AffineW o.iss.bytes
  subP : Affine o.sub.present
  subL : Affine o.sub.len
  subB : AffineW o.sub.bytes
  audP : Affine o.aud.present
  audL : Affine o.aud.len
  audB : AffineW o.aud.bytes
  azpP : Affine o.azp.present
  azpL : Affine o.azp.len
  azpB : AffineW o.azp.bytes
  hdP : Affine o.hd.present
  hdL : Affine o.hd.len
  hdB : AffineW o.hd.bytes
  emailP : Affine o.email.present
  emailL : Affine o.email.len
  emailB : AffineW o.email.bytes
  evP : Affine o.emailVerified.present
  evV : Affine o.emailVerified.value
  noncePr : Affine o.nonce.present
  nonceL : Affine o.nonce.len
  nonceB : AffineW o.nonce.bytes
  atHashP : Affine o.atHash.present
  atHashL : Affine o.atHash.len
  atHashB : AffineW o.atHash.bytes
  iatP : Affine o.iat.present
  iatN : Affine o.iat.negative
  iatL : Affine o.iat.len
  iatD : AffineW o.iat.digits
  expP : Affine o.exp.present
  expN : Affine o.exp.negative
  expL : Affine o.exp.len
  expD : AffineW o.exp.digits

set_option maxHeartbeats 1000000 in
theorem affineSlots_varFromOffset (n : ℕ) :
    AffineSlots (varFromOffset Output n : Var Output (F circomPrime)) := by
  constructor <;>
    (simp only [circuit_norm]; first | exact Affine.var _ | exact affineW_varFromOffset _ _)

theorem affineSlots_witnessIR_output
    (ir : Witgen.WitgenIR (F circomPrime) (size Output)) (n : ℕ) :
    AffineSlots ((witnessIR Output ir).output n) := by
  show AffineSlots (varFromOffset Output n : Var Output (F circomPrime))
  exact affineSlots_varFromOffset n

/-! ### The per-position signals -/

/-- Affineness of the four signal blocks one `Step` returns. -/
structure AffineSig (o : Step.Outputs (Expression (F circomPrime))) : Prop where
  match_ : AffineW o.match_
  vEmitK : AffineW o.vEmitK
  minusK : AffineW o.minusK
  trueK : Affine o.trueK

set_option maxHeartbeats 1000000 in
theorem affineSig_sub_step_output (inp : Var Step.Inputs (F circomPrime)) (n : ℕ) :
    AffineSig ((subcircuitWithAssertion Step.circuit inp).output n) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩ <;>
    (simp only [circuit_norm, Step.circuit]; exact Affine.var _)

/-- Every position of the `Circuit.map` of `Step`s returns an affine signal block. -/
def AffineSigs (sigs : Vector (Var Step.Outputs (F circomPrime)) bufferLen) : Prop :=
  ∀ (i : ℕ) (hi : i < bufferLen), AffineSig sigs[i]

theorem affineSigs_map_output
    (body : Fin bufferLen → Circuit (F circomPrime) (Var Step.Outputs (F circomPrime)))
    (constant : Circuit.ConstantLength body)
    (h : ∀ i n, AffineSig ((body i).output n)) (n : ℕ) :
    AffineSigs ((Circuit.map (Vector.finRange bufferLen) body constant).output n) := by
  intro i hi
  rw [Circuit.map.output_eq, Vector.getElem_mapIdx]
  exact h _ _

theorem affine_sumOver {sigs : Vector (Var Step.Outputs (F circomPrime)) bufferLen}
    {f : Var Step.Outputs (F circomPrime) → Expression (F circomPrime)}
    (h : ∀ i : Fin bufferLen, Affine (f sigs[i])) : Affine (sumOver sigs f) :=
  affine_finFoldl' _ 0 Affine.zero fun _acc i hacc => Affine.add hacc (h i)

end Cost
end Solution.JSONExtract
