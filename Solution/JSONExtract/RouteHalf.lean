import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Model
import Solution.JSONExtract.RouteSlot
import Solution.JSONExtract.Interfaces

/-!
# Routing into five output slots (`JSONExtract`)

`RouteSlot n` selects the cell of one slot the offset one-hot points at,
gated by the slot's claim flag.  This gadget is five of them, summed: one half
of the ten string/integer slots of the output.  `Step` pins the routed value
against the sum of the two halves.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (ofsMax)

set_option linter.unusedSimpArgs false

namespace RouteHalf

structure Inputs (n0 n1 n2 n3 n4 : ℕ) (F : Type) where
  claim0 : F
  claim1 : F
  claim2 : F
  claim3 : F
  claim4 : F
  ofsOH : Vector F ofsMax
  cells0 : Vector F n0
  cells1 : Vector F n1
  cells2 : Vector F n2
  cells3 : Vector F n3
  cells4 : Vector F n4
deriving ProvableStruct

structure Outputs (F : Type) where
  /-- the selected cell, summed over the five slots -/
  sel : F
  /-- the "selected cell exists", summed over the five slots -/
  exists_ : F
deriving ProvableStruct

variable {n0 n1 n2 n3 n4 : ℕ} [NeZero n0] [NeZero n1] [NeZero n2] [NeZero n3] [NeZero n4]

def main (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax) (h3 : n3 ≤ ofsMax)
    (h4 : n4 ≤ ofsMax) (inp : Var (Inputs n0 n1 n2 n3 n4) (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let r0 ← RouteSlot.circuit n0 h0 { claimFlag := inp.claim0, ofsOH := inp.ofsOH, cells := inp.cells0 }
  let r1 ← RouteSlot.circuit n1 h1 { claimFlag := inp.claim1, ofsOH := inp.ofsOH, cells := inp.cells1 }
  let r2 ← RouteSlot.circuit n2 h2 { claimFlag := inp.claim2, ofsOH := inp.ofsOH, cells := inp.cells2 }
  let r3 ← RouteSlot.circuit n3 h3 { claimFlag := inp.claim3, ofsOH := inp.ofsOH, cells := inp.cells3 }
  let r4 ← RouteSlot.circuit n4 h4 { claimFlag := inp.claim4, ofsOH := inp.ofsOH, cells := inp.cells4 }
  return { sel := r0.sel + r1.sel + r2.sel + r3.sel + r4.sel,
           exists_ := r0.exists_ + r1.exists_ + r2.exists_ + r3.exists_ + r4.exists_ }

instance elaborated (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax) (h3 : n3 ≤ ofsMax)
    (h4 : n4 ≤ ofsMax) :
    ElaboratedCircuit (F circomPrime) (Inputs n0 n1 n2 n3 n4) Outputs (main h0 h1 h2 h3 h4) := by
  elaborate_circuit

def Assumptions (_ : Inputs n0 n1 n2 n3 n4 (F circomPrime)) : Prop := True

def Spec (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax) (h3 : n3 ≤ ofsMax)
    (h4 : n4 ≤ ofsMax) (inp : Inputs n0 n1 n2 n3 n4 (F circomPrime))
    (out : Outputs (F circomPrime)) : Prop :=
  out.sel = inp.claim0 * slotSel n0 h0 inp.ofsOH inp.cells0
      + inp.claim1 * slotSel n1 h1 inp.ofsOH inp.cells1
      + inp.claim2 * slotSel n2 h2 inp.ofsOH inp.cells2
      + inp.claim3 * slotSel n3 h3 inp.ofsOH inp.cells3
      + inp.claim4 * slotSel n4 h4 inp.ofsOH inp.cells4 ∧
  out.exists_ = inp.claim0 * slotEx n0 h0 inp.ofsOH + inp.claim1 * slotEx n1 h1 inp.ofsOH
      + inp.claim2 * slotEx n2 h2 inp.ofsOH + inp.claim3 * slotEx n3 h3 inp.ofsOH
      + inp.claim4 * slotEx n4 h4 inp.ofsOH

theorem soundness (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax) (h3 : n3 ≤ ofsMax)
    (h4 : n4 ≤ ofsMax) :
    Soundness (F circomPrime) (main h0 h1 h2 h3 h4) Assumptions (Spec h0 h1 h2 h3 h4) := by
  circuit_proof_start [Assumptions, Spec, main]
  simp only [routeSlot_Assumptions, routeSlot_Spec, routeSlot_localLength, routeSlot_output,
    routeSlot_channelsWithRequirements, RouteSlot.Spec, eval_routeSlotOut', slotSel, slotEx,
    true_implies, true_or,
    and_true, and_self, Expression.eval] at h_holds ⊢
  obtain ⟨⟨s0, x0⟩, ⟨s1, x1⟩, ⟨s2, x2⟩, ⟨s3, x3⟩, ⟨s4, x4⟩⟩ := h_holds
  exact ⟨by rw [s0, s1, s2, s3, s4], by rw [x0, x1, x2, x3, x4]⟩

theorem completeness (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax) (h3 : n3 ≤ ofsMax)
    (h4 : n4 ≤ ofsMax) :
    Completeness (F circomPrime) (main h0 h1 h2 h3 h4) Assumptions := by
  circuit_proof_start [Assumptions, main]
  simp only [routeSlot_Assumptions]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

def circuit (n0 n1 n2 n3 n4 : ℕ) [NeZero n0] [NeZero n1] [NeZero n2] [NeZero n3] [NeZero n4]
    (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax) (h3 : n3 ≤ ofsMax)
    (h4 : n4 ≤ ofsMax) : FormalCircuit (F circomPrime) (Inputs n0 n1 n2 n3 n4) Outputs where
  main := main h0 h1 h2 h3 h4
  elaborated := elaborated h0 h1 h2 h3 h4
  Assumptions := Assumptions
  Spec := Spec h0 h1 h2 h3 h4
  soundness := soundness h0 h1 h2 h3 h4
  completeness := completeness h0 h1 h2 h3 h4


/-! ## The bundled interface -/

@[simp] lemma routeHalf_Assumptions (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax)
    (h3 : n3 ≤ ofsMax) (h4 : n4 ≤ ofsMax) (inp : Inputs n0 n1 n2 n3 n4 (F circomPrime)) :
    (circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4).Assumptions inp = True := rfl

@[simp] lemma routeHalf_Spec (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax)
    (h3 : n3 ≤ ofsMax) (h4 : n4 ≤ ofsMax) (inp : Inputs n0 n1 n2 n3 n4 (F circomPrime))
    (o : Outputs (F circomPrime)) :
    (circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4).Spec inp o = Spec h0 h1 h2 h3 h4 inp o := rfl

@[simp] lemma routeHalf_channelsWithRequirements (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax)
    (h2 : n2 ≤ ofsMax) (h3 : n3 ≤ ofsMax) (h4 : n4 ≤ ofsMax) :
    (circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4).channelsWithRequirements = [] := rfl

@[simp] lemma routeHalf_localLength (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax)
    (h3 : n3 ≤ ofsMax) (h4 : n4 ≤ ofsMax) (inp : Var (Inputs n0 n1 n2 n3 n4) (F circomPrime)) :
    (circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4).localLength inp
      = n0 + 2 + (n1 + 2 + (n2 + 2 + (n3 + 2 + (n4 + 2)))) := rfl

@[simp] lemma routeHalf_output (h0 : n0 ≤ ofsMax) (h1 : n1 ≤ ofsMax) (h2 : n2 ≤ ofsMax)
    (h3 : n3 ≤ ofsMax) (h4 : n4 ≤ ofsMax) (inp : Var (Inputs n0 n1 n2 n3 n4) (F circomPrime))
    (i : ℕ) :
    (circuit n0 n1 n2 n3 n4 h0 h1 h2 h3 h4).output inp i
      = { sel := var ⟨i + n0⟩ + var ⟨i + (n0 + 2) + n1⟩ + var ⟨i + (n0 + 2) + (n1 + 2) + n2⟩
            + var ⟨i + (n0 + 2) + (n1 + 2) + (n2 + 2) + n3⟩
            + var ⟨i + (n0 + 2) + (n1 + 2) + (n2 + 2) + (n3 + 2) + n4⟩,
          exists_ := var ⟨i + n0 + 1⟩ + var ⟨i + (n0 + 2) + n1 + 1⟩
            + var ⟨i + (n0 + 2) + (n1 + 2) + n2 + 1⟩
            + var ⟨i + (n0 + 2) + (n1 + 2) + (n2 + 2) + n3 + 1⟩
            + var ⟨i + (n0 + 2) + (n1 + 2) + (n2 + 2) + (n3 + 2) + n4 + 1⟩ } := rfl

/-- `ProvableStruct.eval` pushed through a `RouteHalf` output literal. -/
@[simp] lemma eval_routeHalfOut (env : Environment (F circomPrime))
    (sel ex : Expression (F circomPrime)) :
    ProvableStruct.eval env ({ sel := sel, exists_ := ex } : Var Outputs (F circomPrime))
      = { sel := Expression.eval env sel, exists_ := Expression.eval env ex } := by
  simp [circuit_norm]

end RouteHalf
end Solution.JSONExtract
