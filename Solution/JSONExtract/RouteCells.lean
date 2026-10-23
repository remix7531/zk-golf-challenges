import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Solution.JSONExtract.Model
import Solution.JSONExtract.RouteHalf
import Solution.JSONExtract.Interfaces

/-!
# Routing the emitted value into the output slots (`JSONExtract`)

The ten string/integer slots of the output, in two halves of five
(`RouteHalf`), and the two rows that use them: the routed value must equal the
cell the claim register and the offset select, and that cell must exist, which
is what caps a value at its slot's width.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nClaims ofsMax)

set_option linter.unusedSimpArgs false

namespace RouteCells

structure Inputs (F : Type) where
  /-- the emitted value is routed to a known string/int claim's slot -/
  write : F
  /-- the routed value -/
  valOut : F
  claimPrev : Vector F nClaims
  ofsOH : Vector F ofsMax
  iss : Vector F 32
  sub : Vector F 32
  aud : Vector F 128
  azp : Vector F 128
  hd : Vector F 64
  email : Vector F 128
  nonce : Vector F 64
  atHash : Vector F 64
  iat : Vector F 12
  exp : Vector F 12
deriving ProvableStruct

def hA : (32 : ℕ) ≤ ofsMax := by decide
def hB : (64 : ℕ) ≤ ofsMax := by decide
def hC : (128 : ℕ) ≤ ofsMax := by decide
def hD : (12 : ℕ) ≤ ofsMax := by decide

def main (inp : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let a ← RouteHalf.circuit 32 32 128 128 64 hA hA hC hC hB {
    claim0 := inp.claimPrev[0], claim1 := inp.claimPrev[1], claim2 := inp.claimPrev[2],
    claim3 := inp.claimPrev[3], claim4 := inp.claimPrev[4], ofsOH := inp.ofsOH,
    cells0 := inp.iss, cells1 := inp.sub, cells2 := inp.aud, cells3 := inp.azp,
    cells4 := inp.hd }
  let b ← RouteHalf.circuit 128 64 64 12 12 hC hB hB hD hD {
    claim0 := inp.claimPrev[5], claim1 := inp.claimPrev[7], claim2 := inp.claimPrev[8],
    claim3 := inp.claimPrev[9], claim4 := inp.claimPrev[10], ofsOH := inp.ofsOH,
    cells0 := inp.email, cells1 := inp.nonce, cells2 := inp.atHash, cells3 := inp.iat,
    cells4 := inp.exp }
  assertZero (inp.write * (a.sel + b.sel - inp.valOut))
  assertZero (inp.write * (a.exists_ + b.exists_ - 1))

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

def Assumptions (_ : Inputs (F circomPrime)) : Prop := True

/-- The cell the claim register and the offset select, over the ten slots. -/
def selected (inp : Inputs (F circomPrime)) : F circomPrime :=
  inp.claimPrev[0] * slotSel 32 hA inp.ofsOH inp.iss
    + inp.claimPrev[1] * slotSel 32 hA inp.ofsOH inp.sub
    + inp.claimPrev[2] * slotSel 128 hC inp.ofsOH inp.aud
    + inp.claimPrev[3] * slotSel 128 hC inp.ofsOH inp.azp
    + inp.claimPrev[4] * slotSel 64 hB inp.ofsOH inp.hd
    + (inp.claimPrev[5] * slotSel 128 hC inp.ofsOH inp.email
      + inp.claimPrev[7] * slotSel 64 hB inp.ofsOH inp.nonce
      + inp.claimPrev[8] * slotSel 64 hB inp.ofsOH inp.atHash
      + inp.claimPrev[9] * slotSel 12 hD inp.ofsOH inp.iat
      + inp.claimPrev[10] * slotSel 12 hD inp.ofsOH inp.exp)

/-- The selected cell exists (the offset is within the selected slot's cap). -/
def existsIn (inp : Inputs (F circomPrime)) : F circomPrime :=
  inp.claimPrev[0] * slotEx 32 hA inp.ofsOH + inp.claimPrev[1] * slotEx 32 hA inp.ofsOH
    + inp.claimPrev[2] * slotEx 128 hC inp.ofsOH + inp.claimPrev[3] * slotEx 128 hC inp.ofsOH
    + inp.claimPrev[4] * slotEx 64 hB inp.ofsOH
    + (inp.claimPrev[5] * slotEx 128 hC inp.ofsOH + inp.claimPrev[7] * slotEx 64 hB inp.ofsOH
      + inp.claimPrev[8] * slotEx 64 hB inp.ofsOH + inp.claimPrev[9] * slotEx 12 hD inp.ofsOH
      + inp.claimPrev[10] * slotEx 12 hD inp.ofsOH)

def Spec (inp : Inputs (F circomPrime)) : Prop :=
  inp.write * (selected inp - inp.valOut) = 0 ∧ inp.write * (existsIn inp - 1) = 0

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, selected, existsIn, main]
  obtain ⟨e_write, e_valOut, e_claimPrev, e_ofsOH, e_iss, e_sub, e_aud, e_azp, e_hd, e_email,
    e_nonce, e_atHash, e_iat, e_exp⟩ := h_input
  have hcl : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env (input_var_claimPrev[i]'h) = input_claimPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_claimPrev i h
    simpa [Vector.getElem_map] using this
  simp only [RouteHalf.routeHalf_Assumptions, RouteHalf.routeHalf_Spec, RouteHalf.routeHalf_localLength, RouteHalf.routeHalf_output,
    RouteHalf.routeHalf_channelsWithRequirements, RouteHalf.Spec, RouteHalf.eval_routeHalfOut, true_implies,
    true_or, and_true, and_self, Expression.eval, hcl, e_write, e_valOut, e_ofsOH, e_iss,
    e_sub, e_aud, e_azp, e_hd, e_email, e_nonce, e_atHash, e_iat, e_exp] at h_holds ⊢
  obtain ⟨⟨sa, xa⟩, ⟨sb, xb⟩, hsel, hex⟩ := h_holds
  rw [sa, sb] at hsel
  rw [xa, xb] at hex
  exact ⟨hsel, hex⟩

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec, selected, existsIn, main]
  obtain ⟨e_write, e_valOut, e_claimPrev, e_ofsOH, e_iss, e_sub, e_aud, e_azp, e_hd, e_email,
    e_nonce, e_atHash, e_iat, e_exp⟩ := h_input
  have hcl : ∀ (i : ℕ) (h : i < nClaims),
      Expression.eval env.toEnvironment (input_var_claimPrev[i]'h) = input_claimPrev[i]'h := by
    intro i h
    have := Vector.ext_iff.mp e_claimPrev i h
    simpa [Vector.getElem_map] using this
  obtain ⟨s1, s2⟩ := h_spec
  simp only [RouteHalf.routeHalf_Assumptions, RouteHalf.routeHalf_Spec, RouteHalf.routeHalf_localLength, RouteHalf.routeHalf_output,
    RouteHalf.Spec, RouteHalf.eval_routeHalfOut, true_and, and_true, true_implies, Expression.eval,
    hcl, e_write, e_valOut, e_ofsOH, e_iss, e_sub, e_aud, e_azp, e_hd, e_email, e_nonce,
    e_atHash, e_iat, e_exp] at h_env ⊢
  obtain ⟨⟨sa, xa⟩, ⟨sb, xb⟩⟩ := h_env
  refine ⟨?_, ?_⟩
  · rw [sa, sb]; linear_combination s1
  · rw [xa, xb]; linear_combination s2

def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
}

end RouteCells
end Solution.JSONExtract
