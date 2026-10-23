import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Mul
import Solution.JSONExtract.Model
import Solution.JSONExtract.ByteClass
import Solution.JSONExtract.OneHot
import Solution.JSONExtract.OneHotInterface
import Solution.JSONExtract.RouteSlot
import Solution.JSONExtract.SubAutomaton
import Solution.JSONExtract.MainAutomaton
import Solution.JSONExtract.Matcher

/-!
# The bundled interfaces of the `JSONExtract` gadgets

The `Assumptions` / `Spec` / `localLength` / `output` of every gadget one
position calls, as `rfl` lemmas, so that no caller ever unfolds a child's
`main` and the offset arithmetic stays linear.  It also carries `classesOf`,
the byte classifier's output read as a function of the byte value, which is
what `ByteClass.Spec` says about the flags the gadget returns.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Circomlib
open Model (nSt nSub nClaims kIdxMax ofsMax St Sub Claim)
open ByteClass (ind)

/-! ## Interfaces of the gadgets `Step` calls

The bundled `Assumptions`/`Spec`/`localLength`/`output` of every child gadget,
as `rfl` lemmas, so that the `Step` proofs never unfold a child's `main` and
the offset arithmetic stays linear. -/

/-- `2 ^ 17 < p`, for `LessThan 16`. -/
theorem two_pow_17_lt : 2 ^ 17 < circomPrime := by decide

@[simp] lemma byteClass_Assumptions (x : F circomPrime) :
    ByteClass.circuit.Assumptions x = (x.val < 256) := rfl

@[simp] lemma byteClass_localLength (x : Var field (F circomPrime)) :
    ByteClass.circuit.localLength x = 108 := rfl

@[simp] lemma byteClass_channelsWithRequirements :
    ByteClass.circuit.channelsWithRequirements = [] := rfl

/-- The classifier returns exactly the value-level classes of its byte. -/
@[simp] lemma byteClass_Spec_iff (x : F circomPrime) (o : ByteClass.Outputs (F circomPrime)) :
    ByteClass.circuit.Spec x o ↔ o = classesOf x.val := by
  obtain ⟨b, c⟩ := o
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := b
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := c
  simp only [show ByteClass.circuit.Spec = ByteClass.Spec from rfl, ByteClass.Spec, classesOf,
    ByteClass.Outputs.mk.injEq, ByteClass.Bytes.mk.injEq, ByteClass.Classes.mk.injEq, and_assoc]

@[simp] lemma matcher_Assumptions (k : Claim) (inp : Matcher.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) : (Matcher.circuit k).Assumptions inp d = True := rfl

@[simp] lemma matcher_ProverAssumptions (k : Claim) (inp : Matcher.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) (h : ProverHint (F circomPrime)) :
    (Matcher.circuit k).ProverAssumptions inp d h = Matcher.ProverAssumptions k inp := rfl

@[simp] lemma matcher_ProverSpec (k : Claim) (inp : Matcher.Inputs (F circomPrime))
    (o : F circomPrime) (h : ProverHint (F circomPrime)) :
    (Matcher.circuit k).ProverSpec inp o h = True := rfl

@[simp] lemma matcher_Spec (k : Claim) (inp : Matcher.Inputs (F circomPrime))
    (o : F circomPrime) (d : ProverData (F circomPrime)) :
    (Matcher.circuit k).Spec inp o d = Matcher.Spec k inp o := rfl

@[simp] lemma matcher_localLength (k : Claim) (inp : Var Matcher.Inputs (F circomPrime)) :
    (Matcher.circuit k).localLength inp = 8 := rfl

@[simp] lemma matcher_output (k : Claim) (inp : Var Matcher.Inputs (F circomPrime)) (i : ℕ) :
    (Matcher.circuit k).output inp i = var ⟨i + 7⟩ := rfl

@[simp] lemma matcher_channelsWithRequirements (k : Claim) :
    (Matcher.circuit k).channelsWithRequirements = [] := rfl

@[simp] lemma routeSlot_Assumptions (n : ℕ) [NeZero n] (hn : n ≤ ofsMax)
    (inp : RouteSlot.Inputs n (F circomPrime)) : (RouteSlot.circuit n hn).Assumptions inp = True :=
  rfl

@[simp] lemma routeSlot_Spec (n : ℕ) [NeZero n] (hn : n ≤ ofsMax)
    (inp : RouteSlot.Inputs n (F circomPrime)) (o : RouteSlot.Outputs (F circomPrime)) :
    (RouteSlot.circuit n hn).Spec inp o = RouteSlot.Spec n hn inp o := rfl

@[simp] lemma routeSlot_localLength (n : ℕ) [NeZero n] (hn : n ≤ ofsMax)
    (inp : Var (RouteSlot.Inputs n) (F circomPrime)) :
    (RouteSlot.circuit n hn).localLength inp = n + 2 := rfl

@[simp] lemma routeSlot_output (n : ℕ) [NeZero n] (hn : n ≤ ofsMax)
    (inp : Var (RouteSlot.Inputs n) (F circomPrime)) (i : ℕ) :
    (RouteSlot.circuit n hn).output inp i = { sel := var ⟨i + n⟩, exists_ := var ⟨i + n + 1⟩ } := rfl

@[simp] lemma routeSlot_channelsWithRequirements (n : ℕ) [NeZero n] (hn : n ≤ ofsMax) :
    (RouteSlot.circuit n hn).channelsWithRequirements = [] := rfl

@[simp] lemma subAutomaton_Assumptions (inp : SubAutomaton.Inputs (F circomPrime)) :
    SubAutomaton.circuit.Assumptions inp = True := rfl

@[simp] lemma subAutomaton_Spec (inp : SubAutomaton.Inputs (F circomPrime)) :
    SubAutomaton.circuit.Spec inp = SubAutomaton.Spec inp := rfl

@[simp] lemma subAutomaton_localLength (inp : Var SubAutomaton.Inputs (F circomPrime)) :
    SubAutomaton.circuit.localLength inp = 49 := rfl

@[simp] lemma mainAutomaton_Assumptions (inp : MainAutomaton.Inputs (F circomPrime)) :
    MainAutomaton.circuit.Assumptions inp = True := rfl

@[simp] lemma mainAutomaton_Spec (inp : MainAutomaton.Inputs (F circomPrime)) :
    MainAutomaton.circuit.Spec inp = MainAutomaton.Spec inp := rfl

@[simp] lemma mainAutomaton_localLength (inp : Var MainAutomaton.Inputs (F circomPrime)) :
    MainAutomaton.circuit.localLength inp = 99 := rfl

@[simp] lemma lessThan_Assumptions (hn : 2 ^ 17 < circomPrime) (x y : F circomPrime) :
    (LessThan.circuit (p := circomPrime) 16 hn).Assumptions (x, y)
      = (x.val < 2 ^ 16 ∧ y.val ≤ 2 ^ 16) := rfl

@[simp] lemma lessThan_Spec (hn : 2 ^ 17 < circomPrime) (x y o : F circomPrime) :
    (LessThan.circuit (p := circomPrime) 16 hn).Spec (x, y) o
      = (o = if x.val < y.val then 1 else 0) := rfl

@[simp] lemma lessThan_localLength (hn : 2 ^ 17 < circomPrime)
    (x : Var fieldPair (F circomPrime)) :
    (LessThan.circuit (p := circomPrime) 16 hn).localLength x = 18 := rfl

@[simp] lemma lessThan_output (hn : 2 ^ 17 < circomPrime) (x : Var fieldPair (F circomPrime))
    (i : ℕ) : (LessThan.circuit (p := circomPrime) 16 hn).output x i = var ⟨i + 17⟩ := rfl

@[simp] lemma lessThan_channelsWithRequirements (hn : 2 ^ 17 < circomPrime) :
    (LessThan.circuit (p := circomPrime) 16 hn).channelsWithRequirements = [] := rfl


/-! ## Routing into one slot -/

/-- `ProvableStruct.eval` pushed through a `RouteSlot` output literal. -/
@[simp] lemma eval_routeSlotOut' (env : Environment (F circomPrime))
    (sel ex : Expression (F circomPrime)) :
    ProvableStruct.eval env ({ sel := sel, exists_ := ex } : Var RouteSlot.Outputs (F circomPrime))
      = { sel := Expression.eval env sel, exists_ := Expression.eval env ex } := by
  simp [circuit_norm]


/-- The cell of one slot selected by the offset one-hot. -/
def slotSel (n : ℕ) (hn : n ≤ ofsMax) (ofsOH : Vector (F circomPrime) ofsMax)
    (cells : Vector (F circomPrime) n) : F circomPrime :=
  Fin.foldl n (fun acc t => acc + RouteSlot.ofsAt hn ofsOH t * cells[t]) 0

/-- The "the selected cell is inside this slot" flag. -/
def slotEx (n : ℕ) (hn : n ≤ ofsMax) (ofsOH : Vector (F circomPrime) ofsMax) : F circomPrime :=
  Fin.foldl n (fun acc t => acc + RouteSlot.ofsAt hn ofsOH t) 0


end Solution.JSONExtract
