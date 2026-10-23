import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.FilledMask
import Solution.JSONExtract.Theorems

/-!
# Pinning the output slots (`JSONExtract`)

Three assertions, one per slot kind, pin an output slot to the quantities the
end of `main` computes from the run: the presence flag (which they also force
boolean, so a known key occurs at most once), the length, for integer slots
the sign, for the boolean slot the value, and, through `FilledMask`, the
zeroing of every cell at or past the length.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface

namespace StrSlotPin

structure Inputs (n : ℕ) (F : Type) where
  slot : StrSlot n F
  present : F
  len : F
deriving ProvableStruct

def main (n : ℕ) [NeZero n] (inp : Var (Inputs n) (F circomPrime)) : Circuit (F circomPrime) Unit := do
  assertZero (inp.present * (inp.present - 1))
  assertZero (inp.slot.present - inp.present)
  assertZero (inp.slot.len - inp.len)
  FilledMask.circuit n { cells := inp.slot.bytes, len := inp.len }

instance elaborated (n : ℕ) [NeZero n] :
    ElaboratedCircuit (F circomPrime) (Inputs n) unit (main n) := by
  elaborate_circuit

/-- Only the slot width bound, which is `FilledMask`'s (the mask sum must not wrap,
and the witness generator's u64 index comparison must be exact); every call site
instantiates `n` with a small numeral.

Neither the booleanity of the presence flag nor the length bound is assumed: both are
forced by the rows, and `Main.soundness` -- where a cheating prover picks the sums the
pin is fed -- could never discharge them. They are conclusions of `Spec` instead. -/
def Assumptions (n : ℕ) (_inp : Inputs n (F circomPrime)) : Prop :=
  n < 2 ^ 64

def Spec (n : ℕ) (inp : Inputs n (F circomPrime)) : Prop :=
  IsBool inp.present ∧ inp.slot.present = inp.present ∧ inp.slot.len = inp.len ∧
  inp.len.val ≤ n ∧ ∀ t : Fin n, inp.len.val ≤ t.val → inp.slot.bytes[t] = 0

theorem soundness (n : ℕ) [NeZero n] :
    FormalAssertion.Soundness (F circomPrime) (main n) (Assumptions n) (Spec n) := by
  circuit_proof_start [Assumptions, Spec, FilledMask.circuit, FilledMask.Assumptions,
    FilledMask.Spec]
  have hn := h_assumptions
  obtain ⟨h_bool, h_present, h_len, h_mask⟩ := h_holds
  obtain ⟨hlen', hzero⟩ := h_mask hn
  exact ⟨IsBool.iff_mul_sub_one.mpr h_bool, sub_eq_zero.mp h_present, sub_eq_zero.mp h_len,
    hlen', hzero⟩

theorem completeness (n : ℕ) [NeZero n] :
    FormalAssertion.Completeness (F circomPrime) (main n) (Assumptions n) (Spec n) := by
  circuit_proof_start [Assumptions, Spec, FilledMask.circuit, FilledMask.Assumptions,
    FilledMask.Spec]
  have hn := h_assumptions
  obtain ⟨s_bool, s_present, s_len, s_fit, s_zero⟩ := h_spec
  refine ⟨IsBool.iff_mul_sub_one.mp s_bool, ?_, ?_, hn, s_fit, s_zero⟩
  · rw [s_present, sub_self]
  · rw [s_len, sub_self]

def circuit (n : ℕ) [NeZero n] : FormalAssertion (F circomPrime) (Inputs n) := {
  main := main n, elaborated := elaborated n, Assumptions := Assumptions n, Spec := Spec n
  soundness := soundness n
  completeness := completeness n
  exposedChannels_eq := by intro _ _ exposed h; simp at h
  -- the default tactic unfolds `main` before normalizing and blows up on the
  -- `FilledMask` subcircuit; see `Theorems.lean`
  requirementsChannelsLawful := fun _ _ =>
    requirementsChannelsLawful_of_noChannels rfl rfl
}

end StrSlotPin

namespace IntSlotPin

structure Inputs (n : ℕ) (F : Type) where
  slot : IntSlot n F
  present : F
  negative : F
  len : F
deriving ProvableStruct

def main (n : ℕ) [NeZero n] (inp : Var (Inputs n) (F circomPrime)) : Circuit (F circomPrime) Unit := do
  assertZero (inp.present * (inp.present - 1))
  assertZero (inp.slot.present - inp.present)
  assertZero (inp.slot.negative - inp.negative)
  assertZero (inp.slot.len - inp.len)
  FilledMask.circuit n { cells := inp.slot.digits, len := inp.len }

instance elaborated (n : ℕ) [NeZero n] :
    ElaboratedCircuit (F circomPrime) (Inputs n) unit (main n) := by
  elaborate_circuit

/-- Only the slot width bound (see `StrSlotPin.Assumptions`); booleanity of the
presence flag and the length bound are conclusions, not assumptions. -/
def Assumptions (n : ℕ) (_inp : Inputs n (F circomPrime)) : Prop :=
  n < 2 ^ 64

def Spec (n : ℕ) (inp : Inputs n (F circomPrime)) : Prop :=
  IsBool inp.present ∧ inp.slot.present = inp.present ∧ inp.slot.negative = inp.negative ∧
  inp.slot.len = inp.len ∧ inp.len.val ≤ n ∧ ∀ t : Fin n, inp.len.val ≤ t.val → inp.slot.digits[t] = 0

theorem soundness (n : ℕ) [NeZero n] :
    FormalAssertion.Soundness (F circomPrime) (main n) (Assumptions n) (Spec n) := by
  circuit_proof_start [Assumptions, Spec, FilledMask.circuit, FilledMask.Assumptions,
    FilledMask.Spec]
  have hn := h_assumptions
  obtain ⟨h_bool, h_present, h_neg, h_len, h_mask⟩ := h_holds
  obtain ⟨hlen', hzero⟩ := h_mask hn
  exact ⟨IsBool.iff_mul_sub_one.mpr h_bool, sub_eq_zero.mp h_present, sub_eq_zero.mp h_neg,
    sub_eq_zero.mp h_len, hlen', hzero⟩

theorem completeness (n : ℕ) [NeZero n] :
    FormalAssertion.Completeness (F circomPrime) (main n) (Assumptions n) (Spec n) := by
  circuit_proof_start [Assumptions, Spec, FilledMask.circuit, FilledMask.Assumptions,
    FilledMask.Spec]
  have hn := h_assumptions
  obtain ⟨s_bool, s_present, s_neg, s_len, s_fit, s_zero⟩ := h_spec
  refine ⟨IsBool.iff_mul_sub_one.mp s_bool, ?_, ?_, ?_, hn, s_fit, s_zero⟩
  · rw [s_present, sub_self]
  · rw [s_neg, sub_self]
  · rw [s_len, sub_self]

def circuit (n : ℕ) [NeZero n] : FormalAssertion (F circomPrime) (Inputs n) := {
  main := main n, elaborated := elaborated n, Assumptions := Assumptions n, Spec := Spec n
  soundness := soundness n
  completeness := completeness n
  exposedChannels_eq := by intro _ _ exposed h; simp at h
  -- the default tactic unfolds `main` before normalizing and blows up on the
  -- `FilledMask` subcircuit; see `Theorems.lean`
  requirementsChannelsLawful := fun _ _ =>
    requirementsChannelsLawful_of_noChannels rfl rfl
}

end IntSlotPin

namespace BoolSlotPin

structure Inputs (F : Type) where
  slot : BoolSlot F
  present : F
  value : F
deriving ProvableStruct

def main (inp : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  assertZero (inp.present * (inp.present - 1))
  assertZero (inp.slot.present - inp.present)
  assertZero (inp.slot.value - inp.value)

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main := by
  elaborate_circuit

/-- Nothing: booleanity of the presence flag is forced by the first row, so it is a
conclusion (see `StrSlotPin.Assumptions`). -/
def Assumptions (_inp : Inputs (F circomPrime)) : Prop := True

def Spec (inp : Inputs (F circomPrime)) : Prop :=
  IsBool inp.present ∧ inp.slot.present = inp.present ∧ inp.slot.value = inp.value

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨h_bool, h_present, h_value⟩ := h_holds
  exact ⟨IsBool.iff_mul_sub_one.mpr h_bool, sub_eq_zero.mp h_present, sub_eq_zero.mp h_value⟩

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [Assumptions, Spec]
  obtain ⟨s_bool, s_present, s_value⟩ := h_spec
  refine ⟨IsBool.iff_mul_sub_one.mp s_bool, ?_, ?_⟩
  · rw [s_present, sub_self]
  · rw [s_value, sub_self]

def circuit : FormalAssertion (F circomPrime) Inputs := {
  main, elaborated, Assumptions, Spec
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
  exposedChannels_eq := by intro _ _ exposed h; simp at h
  -- see the note on `StrSlotPin.circuit`
  requirementsChannelsLawful := fun _ _ =>
    requirementsChannelsLawful_of_noChannels rfl rfl
}

end BoolSlotPin
end Solution.JSONExtract
