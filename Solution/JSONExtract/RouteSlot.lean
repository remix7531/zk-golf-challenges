import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Mul
import Solution.JSONExtract.Theorems
import Solution.JSONExtract.Model

/-!
# Routing into one output slot (`JSONExtract`)

For one output slot of `n` cells, `RouteSlot n` computes the cell selected by
the offset one-hot, gated by the slot's claim flag
(`sel = claim · Σ_t ofsOH[t]·cell[t]`), and the "selected cell exists" flag
(`exists = claim · Σ_{t<n} ofsOH[t]`). `Step` sums these over the ten slots
to pin the routed value and to enforce the cap.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (ofsMax)

namespace RouteSlot

structure Inputs (n : ℕ) (F : Type) where
  claimFlag : F
  ofsOH : Vector F ofsMax
  cells : Vector F n
deriving ProvableStruct

structure Outputs (F : Type) where
  sel : F
  exists_ : F
deriving ProvableStruct

/-- Entry `t` of the offset one-hot, for `t` below the slot width. -/
def ofsAt {n : ℕ} {F : Type} (hn : n ≤ ofsMax) (ofsOH : Vector F ofsMax) (t : Fin n) : F :=
  ofsOH[t.val]'(lt_of_lt_of_le t.isLt hn)

def main (n : ℕ) [NeZero n] (hn : n ≤ ofsMax) (inp : Var (Inputs n) (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let prods ← Circuit.map (Vector.finRange n) fun t =>
    Mul.circuit { a := ofsAt hn inp.ofsOH t, b := inp.cells[t] }
  let sel ← Mul.circuit { a := inp.claimFlag, b := Fin.foldl n (fun acc t => acc + prods[t]) 0 }
  let ofsSum := Fin.foldl n (fun acc t => acc + ofsAt hn inp.ofsOH t) 0
  let exists_ ← Mul.circuit { a := inp.claimFlag, b := ofsSum }
  return { sel := sel, exists_ := exists_ }

instance elaborated (n : ℕ) [NeZero n] (hn : n ≤ ofsMax) :
    ElaboratedCircuit (F circomPrime) (Inputs n) Outputs (main n hn) := by
  elaborate_circuit

def Assumptions (n : ℕ) (_ : Inputs n (F circomPrime)) : Prop := True

def Spec (n : ℕ) (hn : n ≤ ofsMax) (inp : Inputs n (F circomPrime))
    (o : Outputs (F circomPrime)) : Prop :=
  o.sel = inp.claimFlag * (Fin.foldl n (fun acc t => acc + ofsAt hn inp.ofsOH t * inp.cells[t]) 0) ∧
  o.exists_ = inp.claimFlag * (Fin.foldl n (fun acc t => acc + ofsAt hn inp.ofsOH t) 0)

theorem soundness (n : ℕ) [NeZero n] (hn : n ≤ ofsMax) :
    Soundness (F circomPrime) (main n hn) (Assumptions n) (Spec n hn) := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨rfl, rfl, rfl⟩ := h_input
  simp only [Mul.circuit_Assumptions, Mul.circuit_Spec, Mul.circuit_localLength,
    Mul.circuit_output, Mul.circuit_channelsWithRequirements, mul_one,
    forall_const, true_or, and_true, Expression.eval,
    Vector.getElem_map, ofsAt] at h_holds ⊢
  obtain ⟨h_prod, h_sel, h_ex⟩ := h_holds
  simp only [eval_foldl_sum] at h_sel h_ex
  simp only [foldl_add_eq_sum]
  refine ⟨?_, h_ex⟩
  rw [h_sel]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Vector.getElem_mapIdx, Expression.eval]
  exact h_prod t

theorem completeness (n : ℕ) [NeZero n] (hn : n ≤ ofsMax) :
    Completeness (F circomPrime) (main n hn) (Assumptions n) := by
  circuit_proof_start [Assumptions]
  simp only [Mul.circuit_Assumptions]
  exact ⟨fun _ => trivial, trivial, trivial⟩

def circuit (n : ℕ) [NeZero n] (hn : n ≤ ofsMax) :
    FormalCircuit (F circomPrime) (Inputs n) Outputs where
  main := main n hn
  elaborated := elaborated n hn
  Assumptions := Assumptions n
  Spec := Spec n hn
  soundness := soundness n hn
  completeness := completeness n hn

end RouteSlot
end Solution.JSONExtract
