import Solution.JSONExtract.StepModel
import Solution.JSONExtract.Witgen

/-!
# The honest run, at the model level (`JSONExtract`)

Everything `Main`'s loop invariant needs about `Model.run` that is not about the
circuit: the successor table of the main automaton, the frozen tail past `len`,
the well-formedness invariant `Step.WFRegs` along the run, and the counting
argument that makes the offset register of an emitting position the number of
values already routed to the claim.

Nothing here mentions a circuit, an environment or an offset.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSt nSub nClaims kIdxMax ofsMax St Sub Claim Regs)

namespace RunTheory

open Model

/-! ## The successor table of the main automaton -/

/-- The states `Model.stepSt` can move to from `s`. -/
def succSt (s : St) : List St :=
  if s = St.PRE then [St.PRE, St.OBJ]
  else if s = St.OBJ then [St.OBJ, St.KEY, St.END]
  else if s = St.KEY then [St.AKEY, St.KEY]
  else if s = St.AKEY then [St.AKEY, St.PVAL]
  else if s = St.PVAL then [St.PVAL, St.STR, St.NSIGN, St.NZERO, St.NINT, St.T1, St.F1, St.N1]
  else if s = St.STR then [St.AVAL, St.STR]
  else if s = St.NSIGN then [St.NZERO, St.NINT]
  else if s = St.NZERO then [St.NDOT, St.NE, St.AVAL, St.SEP, St.END]
  else if s = St.NINT then [St.NINT, St.NDOT, St.NE, St.AVAL, St.SEP, St.END]
  else if s = St.NDOT then [St.NFRAC]
  else if s = St.NFRAC then [St.NFRAC, St.NE, St.AVAL, St.SEP, St.END]
  else if s = St.NE then [St.NESIGN, St.NEXP]
  else if s = St.NESIGN then [St.NEXP]
  else if s = St.NEXP then [St.NEXP, St.AVAL, St.SEP, St.END]
  else if s = St.T1 then [St.T2]
  else if s = St.T2 then [St.T3]
  else if s = St.T3 then [St.AVAL]
  else if s = St.F1 then [St.F2]
  else if s = St.F2 then [St.F3]
  else if s = St.F3 then [St.F4]
  else if s = St.F4 then [St.AVAL]
  else if s = St.N1 then [St.N2]
  else if s = St.N2 then [St.N3]
  else if s = St.N3 then [St.AVAL]
  else if s = St.AVAL then [St.AVAL, St.SEP, St.END]
  else if s = St.SEP then [St.SEP, St.KEY]
  else [St.END]

set_option maxHeartbeats 2000000 in
/-- The main automaton only takes the edges of `succSt`. -/
theorem stepSt_mem_succ (kind : Kind) (sp : Bool) (s : St) (b : ℕ) (t : St)
    (h : stepSt kind sp s b = some t) : t ∈ succSt s := by
  revert h
  fin_cases s <;>
    simp +decide only [stepSt, afterValue, succSt, St.PRE, St.OBJ, St.KEY, St.AKEY, St.PVAL,
      St.STR, St.NSIGN, St.NZERO, St.NINT, St.NDOT, St.NFRAC, St.NE, St.NESIGN, St.NEXP,
      St.T1, St.T2, St.T3, St.F1, St.F2, St.F3, St.F4, St.N1, St.N2, St.N3, St.AVAL, St.SEP,
      St.END, if_true, if_false, imp_false, not_false_eq_true, forall_const, or_true, true_or,
      List.mem_cons, List.not_mem_nil] <;>
    (intro h; split_ifs at h <;>
      first
        | (rw [Option.some.injEq] at h; subst h; decide)
        | exact absurd h (by simp))

/-- The successor of a step is an edge of the table. -/
theorem step_mem_succ {r r' : Regs} {b : ℕ} (h : step r b = some r') : r'.st ∈ succSt r.st :=
  stepSt_mem_succ _ _ _ _ _ (Step.step_fields h).2.1

/-! ## The frozen tail -/

theorem run_succ (bytes : ℕ → ℕ) (len i : ℕ) :
    run bytes len (i + 1)
      = if i < len then (step (run bytes len i) (bytes i)).getD (run bytes len i)
        else run bytes len i := rfl

theorem run_frozen (bytes : ℕ → ℕ) (len : ℕ) :
    ∀ i, len ≤ i → run bytes len i = run bytes len len := by
  intro i
  induction i with
  | zero => intro h; have : len = 0 := Nat.le_zero.mp h; subst this; rfl
  | succ i ih =>
    intro h
    rcases Nat.lt_or_ge i len with hlt | hge
    · have : len = i + 1 := by omega
      subst this; rfl
    · rw [run_succ, if_neg (by omega)]; exact ih hge

/-- The step of an active position, when it succeeds. -/
theorem run_succ_of_step {bytes : ℕ → ℕ} {len i : ℕ} (hi : i < len) {r' : Regs}
    (h : step (run bytes len i) (bytes i) = some r') : run bytes len (i + 1) = r' := by
  rw [run_succ, if_pos hi, h]; rfl

/-! ## The byte classes that matter for the register updates -/

theorem isWs_isDigit_false {b : ℕ} (h : isWs b = true) : isDigit b = false := by
  simp only [isWs, isDigit, Specs.JSON.space, Specs.JSON.tab, Specs.JSON.lf, Specs.JSON.cr,
    Specs.JSON.digit0, Specs.JSON.digit9, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, not_le] at h ⊢
  omega

/-! ## `PVAL` is always reached with a cleared offset -/

theorem stepSt_pval_pval (kind : Kind) (sp : Bool) (b : ℕ)
    (h : stepSt kind sp St.PVAL b = some St.PVAL) : isWs b = true := by
  by_contra hw
  simp only [Bool.not_eq_true] at hw
  have e : stepSt kind sp St.PVAL b = if isWs b = true then some St.PVAL
      else if (b == Specs.JSON.quote) && (decide (kind = Kind.str) || decide (kind = Kind.unk))
        then some St.STR
      else if (b == Specs.JSON.minus) && (decide (kind = Kind.int) || decide (kind = Kind.unk))
        then some St.NSIGN
      else if (b == Specs.JSON.digit0) && (decide (kind = Kind.int) || decide (kind = Kind.unk))
        then some St.NZERO
      else if isDigitNz b && (decide (kind = Kind.int) || decide (kind = Kind.unk))
        then some St.NINT
      else if (b == Specs.JSON.lowerT) && (decide (kind = Kind.bool) || decide (kind = Kind.unk))
        then some St.T1
      else if (b == Specs.JSON.lowerF) && (decide (kind = Kind.bool) || decide (kind = Kind.unk))
        then some St.F1
      else if (b == Specs.JSON.lowerN) && decide (kind = Kind.unk) then some St.N1
      else none := rfl
  rw [e, if_neg (by simp [hw])] at h
  split_ifs at h <;> exact absurd h (by decide)

/-- `vEmit` only fires at the four states that read a value character. -/
theorem vEmit_states {r : Regs} {b : ℕ} {st' : St} (h : (signals r b st').vEmit = true) :
    r.st = St.STR ∨ r.st = St.PVAL ∨ r.st = St.NSIGN ∨ r.st = St.NINT := by
  have := Step.vEmit_state r b st' h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  tauto

/-- At `PVAL` nothing is emitted from the string sub-automaton, so the value
character is exactly a digit. -/
theorem vEmit_pval (r : Regs) (b : ℕ) (st' : St) (hst : r.st = St.PVAL) :
    (signals r b st').vEmit = isDigit b := by
  simp [signals, hst, Model.inStr, St.PVAL, St.KEY, St.STR, St.NSIGN, St.NINT]

/-- A step into `PVAL` clears the offset: every edge into `PVAL` leaves a state
outside a value (`AKEY` or `PVAL`) and emits nothing. -/
theorem step_pval_ofs {r r' : Regs} {b : ℕ} (h : step r b = some r') (hp : r'.st = St.PVAL) :
    r'.ofs = 0 := by
  obtain ⟨-, hst, -, -, -, hof, -, -⟩ := Step.step_fields h
  rw [hp] at hst
  have hsrc : r.st = St.AKEY ∨ r.st = St.PVAL := by
    have hm := stepSt_mem_succ _ _ _ _ _ hst
    revert hm
    have : ∀ s : St, St.PVAL ∈ succSt s → s = St.AKEY ∨ s = St.PVAL := by decide
    exact this r.st
  have hiv : Step.inValP r.st = false := by
    rcases hsrc with h1 | h1 <;> rw [h1] <;> decide
  have hve : (signals r b r'.st).vEmit = false := by
    by_cases hv : (signals r b r'.st).vEmit = true
    case neg => simpa using hv
    exfalso
    have hstates := vEmit_states hv
    have hpval : r.st = St.PVAL := by
      rcases hsrc with h1 | h1
      · exfalso
        rw [h1] at hstates
        revert hstates; decide
      · exact h1
    have hd : isDigit b = true := by rw [← vEmit_pval r b r'.st hpval]; exact hv
    rw [hpval] at hst
    have hws := stepSt_pval_pval _ _ _ hst
    rw [isWs_isDigit_false hws] at hd
    exact Bool.noConfusion hd
  rw [hof, hiv, hve]
  simp

theorem run_pval_ofs (bytes : ℕ → ℕ) (len : ℕ) :
    ∀ i, (run bytes len i).st = St.PVAL → (run bytes len i).ofs = 0 := by
  intro i
  induction i with
  | zero =>
    intro h
    rw [show run bytes len 0 = Regs.init from rfl] at h
    exact absurd h (by decide)
  | succ i ih =>
    intro h
    rw [run_succ] at h ⊢
    by_cases hlt : i < len
    · rw [if_pos hlt] at h ⊢
      cases hs : step (run bytes len i) (bytes i) with
      | none => simp only [hs, Option.getD] at h ⊢; exact ih h
      | some r' => simp only [hs, Option.getD] at h ⊢; exact step_pval_ofs hs h
    · rw [if_neg hlt] at h ⊢; exact ih h

/-! ## Well-formedness along the run -/

theorem run_wf (bytes : ℕ → ℕ) (len i : ℕ) : Step.WFRegs (run bytes len i) := by
  refine ⟨IR.run_hexAcc_lt bytes len i, ?_, ?_, ?_, run_pval_ofs bytes len i, ?_⟩
  · have := IR.run_kIdx_le bytes len i; simp only [Model.kIdxMax] at this ⊢; omega
  · have := IR.run_ofs_le bytes len i; simp only [Model.ofsMax] at this ⊢; omega
  · exact fun k k' h1 h2 j hj => IR.run_matchInv bytes len i k k' h1 h2 j hj
  · exact IR.run_hexInv bytes len i

/-! ## A frozen position emits nothing

Past `len` the run sits in `END` (that is what `Acceptance` forces), and there
neither a key closes nor a value character is read. -/

theorem signals_end (r : Regs) (b : ℕ) (hst : r.st = St.END) :
    (∀ k : Claim, (signals r b r.st).match_[k] = false) ∧
    (signals r b r.st).vEmit = false ∧ (signals r b r.st).write = false ∧
    (signals r b r.st).minusFlag = false ∧ (signals r b r.st).trueDone = false := by
  refine ⟨fun k => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [signals, hst, Model.inStr, St.END, St.KEY, St.STR, St.PVAL, St.NSIGN, St.NINT,
      St.T3]

/-! ## The byte-class side conditions of the emitting transitions -/

theorem isUnescaped_ne_quote {b : ℕ} (h : isUnescaped b = true) :
    (b == Specs.JSON.quote) = false := by
  simp only [isUnescaped, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  simp only [beq_eq_false_iff_ne, ne_eq]
  exact h.1.2

theorem isDigit_isWs_false {b : ℕ} (h : isDigit b = true) : isWs b = false := by
  simp only [isWs, isDigit, Specs.JSON.space, Specs.JSON.tab, Specs.JSON.lf, Specs.JSON.cr,
    Specs.JSON.digit0, Specs.JSON.digit9, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h ⊢
  omega

/-- Inside a string with the sub-automaton in `PLAIN`, an emission is exactly an
unescaped byte -- in particular never the closing quote. -/
theorem emit_plain (r : Regs) (b : ℕ) (st' : St) (hstr : r.st = St.STR)
    (hsub : r.sub = Sub.PLAIN) : (signals r b st').emit = isUnescaped b := by
  simp [signals, hstr, hsub, Model.inStr, St.STR, St.KEY, Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1]

theorem stepSt_str_stays (kind : Kind) (sp : Bool) (b : ℕ) (t : St)
    (hq : ((b == Specs.JSON.quote) && sp) = false)
    (h : stepSt kind sp St.STR b = some t) : t = St.STR := by
  have e : stepSt kind sp St.STR b =
      if ((b == Specs.JSON.quote) && sp) = true then some St.AVAL else some St.STR := rfl
  rw [e, if_neg (by simp [hq])] at h
  exact (Option.some.inj h).symm

theorem stepSt_nint_digit (kind : Kind) (sp : Bool) (b : ℕ) (t : St) (hd : isDigit b = true)
    (h : stepSt kind sp St.NINT b = some t) : t = St.NINT := by
  have e : stepSt kind sp St.NINT b =
      if isDigit b = true then some St.NINT
      else if (b == Specs.JSON.dot) && decide (kind = Kind.unk) then some St.NDOT
      else if isExpLetter b && decide (kind = Kind.unk) then some St.NE
      else afterValue b := rfl
  rw [e, if_pos hd] at h
  exact (Option.some.inj h).symm

/-- A value character always lands in a state inside the value. -/
theorem emit_next_inVal {r r' : Regs} {b : ℕ} (h : step r b = some r')
    (hv : (signals r b r'.st).vEmit = true) : Step.inValP r'.st = true := by
  obtain ⟨-, hst, -, -, -, -, -, -⟩ := Step.step_fields h
  rw [Step.sig_vEmit, Bool.or_eq_true] at hv
  rcases hv with hse | hde
  · -- inside a string: the byte is emitted, so it is not the closing quote
    simp only [Step.strEmitB, Bool.and_eq_true, decide_eq_true_eq] at hse
    obtain ⟨hemit, hstr⟩ := hse
    have hq : ((b == Specs.JSON.quote) && decide (r.sub = Sub.PLAIN)) = false := by
      by_cases hsub : r.sub = Sub.PLAIN
      · rw [emit_plain r b r.st hstr hsub] at hemit
        simp [isUnescaped_ne_quote hemit]
      · simp [hsub]
    rw [hstr] at hst
    rw [stepSt_str_stays _ _ _ _ hq hst]
    decide
  · -- a digit: the integer states all stay inside the value
    simp only [Step.digitEmitB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hde
    obtain ⟨hd, hstates⟩ := hde
    rcases hstates with (hs | hs) | hs
    · rw [hs] at hst
      have hne : r'.st ≠ St.PVAL := by
        intro hp
        rw [hp] at hst
        have hws := stepSt_pval_pval _ _ _ hst
        rw [isDigit_isWs_false hd] at hws
        exact Bool.noConfusion hws
      have hm := stepSt_mem_succ _ _ _ _ _ hst
      have hall : ∀ t : St, t ∈ succSt St.PVAL → t ≠ St.PVAL → Step.inValP t = true := by decide
      exact hall r'.st hm hne
    · rw [hs] at hst
      have hm := stepSt_mem_succ _ _ _ _ _ hst
      have hall : ∀ t : St, t ∈ succSt St.NSIGN → Step.inValP t = true := by decide
      exact hall r'.st hm
    · rw [hs] at hst
      rw [stepSt_nint_digit _ _ _ _ hd hst]
      decide

/-! ## The offset register counts the values routed to a claim

`Main` reads claim `k`'s slot out of the cells the run writes at the offsets
`ofs` takes, and the two slot pins only say that the cells at or past the slot
length are zero.  So the circuit layer needs to know that the offsets of the
emitting positions of claim `k` are exactly `0, 1, …, slotLen - 1`.  That is
the content of `cinv` below: along the run, an emitting position's offset is
the number of values already routed to `k`.

The argument is one forward induction with three clauses: the offsets so far,
the fact that a live claim register was entered through a key match (which
`presentCount k ≤ 1` then makes unique), and the position's own offset, which
is either the running count -- while the value is being read -- or irrelevant,
because the value is over and the claim register is about to be cleared. -/

section Counting

variable (bytes : ℕ → ℕ) (len : ℕ) (k : Claim)

/-- Position `i` routes a value to claim `k`. -/
def emitsAt (i : ℕ) : Bool :=
  (runSignals bytes len i).vEmit && decide ((run bytes len i).claim = some k)

/-- The number of values routed to claim `k` before position `i`. -/
def emitCount (i : ℕ) : ℕ := ((List.range i).filter (emitsAt bytes len k)).length

theorem emitCount_succ (i : ℕ) :
    emitCount bytes len k (i + 1)
      = emitCount bytes len k i + (if emitsAt bytes len k i = true then 1 else 0) := by
  simp only [emitCount, List.range_succ, List.filter_append, List.length_append,
    List.filter_cons, List.filter_nil]
  by_cases h : emitsAt bytes len k i = true <;> simp [h]

theorem slotLen_eq : slotLen bytes len k = emitCount bytes len k len := rfl

theorem emitsAt_ge {i : ℕ} (h : len ≤ i) : emitsAt bytes len k i = false := by
  simp [emitsAt, runSignals, Nat.not_lt.mpr h]

theorem runSignals_pos {i : ℕ} (hi : i < len) {r' : Regs}
    (hs : step (run bytes len i) (bytes i) = some r') :
    runSignals bytes len i = signals (run bytes len i) (bytes i) r'.st := by
  simp [runSignals, hi, hs]

/-- With at most one member keyed `k`, the key match of `k` happens at most once. -/
theorem match_unique_pos (hpresent : presentCount bytes len k ≤ 1) {a c : ℕ}
    (ha : a < len) (hc : c < len)
    (hma : (runSignals bytes len a).match_[k] = true)
    (hmc : (runSignals bytes len c).match_[k] = true) : a = c := by
  by_contra hne
  set l := (List.range len).filter (fun i => (runSignals bytes len i).match_[k]) with hl_def
  have hma' : a ∈ l := List.mem_filter.mpr ⟨List.mem_range.mpr ha, hma⟩
  have hmc' : c ∈ l := List.mem_filter.mpr ⟨List.mem_range.mpr hc, hmc⟩
  have hsub : ({a, c} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr hma'
    · exact List.mem_toFinset.mpr hmc'
  have h2 : 2 ≤ l.toFinset.card := by
    rw [← Finset.card_pair hne]; exact Finset.card_le_card hsub
  have h3 : l.toFinset.card ≤ l.length := List.toFinset_card_le l
  have : presentCount bytes len k = l.length := rfl
  omega

/-- The loop invariant of the counting argument. -/
def CInv (i : ℕ) : Prop :=
  (∀ j, j < i → emitsAt bytes len k j = true →
      (run bytes len j).ofs = emitCount bytes len k j) ∧
  (((run bytes len i).claim = some k ∨ 0 < emitCount bytes len k i) →
      ∃ a, a < i ∧ (runSignals bytes len a).match_[k] = true) ∧
  ((run bytes len i).claim = some k →
      ((run bytes len i).ofs = emitCount bytes len k i ∧
        (emitCount bytes len k i = 0 ∨ Step.inValP (run bytes len i).st = true))
      ∨ (0 < emitCount bytes len k i ∧
          ((run bytes len i).st = St.AVAL ∨ (run bytes len i).st = St.SEP ∨
            (run bytes len i).st = St.END)))

theorem claimCap_le (k : Claim) : claimCap k ≤ ofsMax - 1 := by revert k; decide

theorem isStr_of_isInt (k : Claim) (h : isIntClaim k = true) : isStrClaim k = false := by
  revert h; revert k; decide

theorem isStr_or_isInt_of_kind (k : Claim)
    (h : kindOf (some k) = Kind.str ∨ kindOf (some k) = Kind.int) :
    isStrClaim k = true ∨ isIntClaim k = true := by
  revert h; revert k; decide

theorem kindOf_str_or_int (hkind : isStrClaim k = true ∨ isIntClaim k = true) :
    kindOf (some k) = Kind.str ∨ kindOf (some k) = Kind.int := by
  simp only [kindOf]
  rcases hkind with h | h
  · exact Or.inl (if_pos h)
  · exact Or.inr (by rw [if_neg (by simp [isStr_of_isInt k h]), if_pos h])

/-- For a known string or integer claim, routing a value *is* emitting one. -/
theorem write_eq_vEmit_sig (hkind : isStrClaim k = true ∨ isIntClaim k = true)
    {r : Regs} {b : ℕ} {st' : St} (hcl : r.claim = some k) :
    (signals r b st').write = (signals r b st').vEmit := by
  have hk := kindOf_str_or_int k hkind
  rw [Step.sig_write, ← Step.sig_vEmit r b st', hcl]
  rcases hk with h | h <;> rw [h] <;> simp

theorem write_eq_vEmit (hkind : isStrClaim k = true ∨ isIntClaim k = true) {i : ℕ}
    (hcl : (run bytes len i).claim = some k) :
    (runSignals bytes len i).write = (runSignals bytes len i).vEmit := by
  by_cases hi : i < len
  · rw [show runSignals bytes len i
        = signals (run bytes len i) (bytes i)
            ((step (run bytes len i) (bytes i)).getD (run bytes len i)).st from by
      simp only [runSignals, if_pos hi]]
    exact write_eq_vEmit_sig k hkind hcl
  · simp [runSignals, hi]

/-- A value routed to a known string or integer claim is a `write`. -/
theorem write_of_emits {r : Regs} {b : ℕ} {st' : St}
    (hkind : isStrClaim k = true ∨ isIntClaim k = true) (hcl : r.claim = some k)
    (hv : (signals r b st').vEmit = true) : (signals r b st').write = true := by
  rw [write_eq_vEmit_sig k hkind hcl]
  exact hv

set_option maxHeartbeats 1000000 in
theorem cinv (hkind : isStrClaim k = true ∨ isIntClaim k = true)
    (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
    (hpresent : presentCount bytes len k ≤ 1) :
    ∀ i, i ≤ len → CInv bytes len k i := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨fun j hj _ => absurd hj (Nat.not_lt_zero j), ?_, ?_⟩
    · rintro (hcl | hlt)
      · exact absurd hcl (by rw [show run bytes len 0 = Regs.init from rfl]; simp [Regs.init])
      · exact absurd hlt (by simp [emitCount])
    · intro hcl
      exact absurd hcl (by rw [show run bytes len 0 = Regs.init from rfl]; simp [Regs.init])
  | succ i ih =>
    intro hle
    have hi : i < len := by omega
    obtain ⟨ihOfs, ihEntry, ihHere⟩ := ih (by omega)
    obtain ⟨r', hs⟩ := Option.isSome_iff_exists.mp (hsteps i hi)
    have hrun : run bytes len (i + 1) = r' := run_succ_of_step hi hs
    have hsg : runSignals bytes len i = signals (run bytes len i) (bytes i) r'.st :=
      runSignals_pos bytes len hi hs
    obtain ⟨-, -, -, -, hclaimEq, hofsEq, -, -⟩ := Step.step_fields hs
    -- an emitting position sits at the running count, inside the value
    have hEmitOfs : emitsAt bytes len k i = true →
        (run bytes len i).ofs = emitCount bytes len k i
          ∧ (emitCount bytes len k i = 0 ∨ Step.inValP (run bytes len i).st = true) := by
      intro he
      simp only [emitsAt, Bool.and_eq_true, decide_eq_true_eq] at he
      obtain ⟨hv, hcl⟩ := he
      rcases ihHere hcl with hb | ⟨-, hpost⟩
      · exact hb
      · exfalso
        rw [hsg] at hv
        rcases vEmit_states hv with h1 | h1 | h1 | h1 <;>
          rcases hpost with h2 | h2 | h2 <;> rw [h1] at h2 <;> exact absurd h2 (by decide)
    refine ⟨?_, ?_, ?_⟩
    · -- the offsets so far
      intro j hj hej
      rcases Nat.lt_or_ge j i with h | h
      · exact ihOfs j h hej
      · have : j = i := by omega
        subst this
        exact (hEmitOfs hej).1
    · -- the claim register was entered through a key match
      rintro hcond
      by_cases hclPrev : (run bytes len i).claim = some k
      · obtain ⟨a, ha, hma⟩ := ihEntry (Or.inl hclPrev)
        exact ⟨a, by omega, hma⟩
      · have hnoEmit : emitsAt bytes len k i = false := by
          simp [emitsAt, hclPrev]
        rw [emitCount_succ, if_neg (by simp [hnoEmit])] at hcond
        rw [Nat.add_zero] at hcond
        rcases hcond with hcl' | hlt
        · -- the claim register turns on here, so this position closes the key of `k`
          rw [hrun, hclaimEq] at hcl'
          have hkc : (signals (run bytes len i) (bytes i) r'.st).keyClose = true := by
            by_contra hkc0
            simp only [Bool.not_eq_true] at hkc0
            rw [hkc0] at hcl'
            simp only [Bool.false_eq_true, if_false] at hcl'
            by_cases hks : (signals (run bytes len i) (bytes i) r'.st).keyStart = true
            · rw [if_pos hks] at hcl'; exact absurd hcl' (by simp)
            · simp only [Bool.not_eq_true] at hks
              rw [hks] at hcl'
              simp only [Bool.false_eq_true, if_false] at hcl'
              exact hclPrev hcl'
          rw [hkc, if_pos rfl] at hcl'
          have hmk := List.find?_some hcl'
          exact ⟨i, by omega, by rw [hsg]; exact hmk⟩
        · obtain ⟨a, ha, hma⟩ := ihEntry (Or.inr hlt)
          exact ⟨a, by omega, hma⟩
    · -- the offset at the next position
      intro hcl'
      rw [hrun] at hcl' ⊢
      rw [emitCount_succ]
      by_cases hclPrev : (run bytes len i).claim = some k
      · -- the claim register stays on
        by_cases he : emitsAt bytes len k i = true
        · -- this position routes a value
          have hetrue := he
          obtain ⟨hofs, hiv⟩ := hEmitOfs he
          simp only [emitsAt, Bool.and_eq_true, decide_eq_true_eq] at he
          obtain ⟨hv, -⟩ := he
          rw [hsg] at hv
          have hwr := write_of_emits k hkind hclPrev hv
          have hcap : (run bytes len i).ofs < claimCap k :=
            Step.step_capOk hs hwr k hclPrev
          have hcapk := claimCap_le k
          have hpre : (if Step.inValP (run bytes len i).st then (run bytes len i).ofs else 0)
              = emitCount bytes len k i := by
            rcases hiv with h0 | h1
            · rw [h0] at hofs
              split <;> simp [hofs, h0]
            · rw [if_pos h1, hofs]
          left
          constructor
          · rw [hofsEq, hv, hpre, if_pos hetrue]
            rw [show (if (true : Bool) = true then 1 else 0) = 1 from rfl]
            simp only [Model.ofsMax] at hcapk hcap hofs ⊢
            omega
          · right
            exact emit_next_inVal hs hv
        · -- this position routes nothing
          simp only [Bool.not_eq_true] at he
          have hv : (signals (run bytes len i) (bytes i) r'.st).vEmit = false := by
            simp only [emitsAt, Bool.and_eq_false_iff, decide_eq_false_iff_not] at he
            rcases he with h | h
            · rw [← hsg]; exact h
            · exact absurd hclPrev h
          rw [if_neg (by simp [he]), Nat.add_zero]
          rcases ihHere hclPrev with ⟨hofs, hiv⟩ | ⟨hpos, hpost⟩
          · rcases hiv with h0 | h1
            · left
              refine ⟨?_, Or.inl h0⟩
              have hr0 : (run bytes len i).ofs = 0 := by rw [hofs, h0]
              rw [hofsEq, hv, hr0, h0]
              simp
            · -- inside the value: the offset is kept
              have hofsr : r'.ofs = emitCount bytes len k i := by
                have hbound := IR.run_ofs_le bytes len i
                rw [hofs] at hbound
                rw [hofsEq, hv, if_pos h1, hofs,
                  show (if (false : Bool) = true then 1 else 0) = 0 from rfl, Nat.add_zero]
                simp only [Model.ofsMax] at hbound ⊢
                omega
              have hm := step_mem_succ hs
              have hall : ∀ s t : St, Step.inValP s = true → t ∈ succSt s →
                  Step.inValP t = true ∨ t = St.AVAL ∨ t = St.SEP ∨ t = St.END := by decide
              rcases hall _ _ h1 hm with h2 | h2
              · exact Or.inl ⟨hofsr, Or.inr h2⟩
              · by_cases hz : emitCount bytes len k i = 0
                · exact Or.inl ⟨hofsr, Or.inl hz⟩
                · exact Or.inr ⟨by omega, h2⟩
          · -- the value is over: stay in the tail
            have hm := step_mem_succ hs
            have hall : ∀ s t : St, (s = St.AVAL ∨ s = St.SEP ∨ s = St.END) → t ∈ succSt s →
                (t = St.AVAL ∨ t = St.SEP ∨ t = St.END) ∨ t = St.KEY := by decide
            rcases hall _ _ hpost hm with h2 | h2
            · exact Or.inr ⟨hpos, h2⟩
            · -- a new key starts, so the claim register is cleared
              exfalso
              have hks : (signals (run bytes len i) (bytes i) r'.st).keyStart = true := by
                simp only [Step.sig_keyStart, h2, decide_true, Bool.true_and, decide_eq_true_eq,
                  ne_eq]
                rcases hpost with h3 | h3 | h3 <;> rw [h3] <;> decide
              have hkc : (signals (run bytes len i) (bytes i) r'.st).keyClose = false := by
                simp only [Step.sig_keyClose, Step.keyCloseB, Bool.and_eq_false_iff,
                  decide_eq_false_iff_not, ne_eq]
                rcases hpost with h3 | h3 | h3 <;> rw [h3] <;> simp +decide
              rw [hclaimEq, hkc] at hcl'
              simp only [Bool.false_eq_true, if_false, hks, if_true] at hcl'
              exact absurd hcl' (by simp)
      · -- the claim register turns on here: nothing has been routed yet
        have hnoEmit : emitsAt bytes len k i = false := by simp [emitsAt, hclPrev]
        rw [if_neg (by simp [hnoEmit]), Nat.add_zero]
        have hzero : emitCount bytes len k i = 0 := by
          by_contra hne
          obtain ⟨a, ha, hma⟩ := ihEntry (Or.inr (by omega))
          -- the key of `k` closes here as well, so two members are keyed `k`
          rw [hclaimEq] at hcl'
          have hkc : (signals (run bytes len i) (bytes i) r'.st).keyClose = true := by
            by_contra hkc0
            simp only [Bool.not_eq_true] at hkc0
            rw [hkc0] at hcl'
            simp only [Bool.false_eq_true, if_false] at hcl'
            by_cases hks : (signals (run bytes len i) (bytes i) r'.st).keyStart = true
            · rw [if_pos hks] at hcl'; exact absurd hcl' (by simp)
            · simp only [Bool.not_eq_true] at hks
              rw [hks] at hcl'
              simp only [Bool.false_eq_true, if_false] at hcl'
              exact hclPrev hcl'
          rw [hkc, if_pos rfl] at hcl'
          have hmk : (runSignals bytes len i).match_[k] = true := by
            rw [hsg]; exact List.find?_some hcl'
          have := match_unique_pos bytes len k hpresent (by omega) hi hma hmk
          omega
        -- at a key close the state is `KEY`, which is outside a value and emits nothing
        have hkc : (signals (run bytes len i) (bytes i) r'.st).keyClose = true := by
          rw [hclaimEq] at hcl'
          by_contra hkc0
          simp only [Bool.not_eq_true] at hkc0
          rw [hkc0] at hcl'
          simp only [Bool.false_eq_true, if_false] at hcl'
          by_cases hks : (signals (run bytes len i) (bytes i) r'.st).keyStart = true
          · rw [if_pos hks] at hcl'; exact absurd hcl' (by simp)
          · simp only [Bool.not_eq_true] at hks
            rw [hks] at hcl'
            simp only [Bool.false_eq_true, if_false] at hcl'
            exact hclPrev hcl'
        have hkey : (run bytes len i).st = St.KEY := by
          simp only [Step.sig_keyClose, Step.keyCloseB, Bool.and_eq_true,
            decide_eq_true_eq] at hkc
          exact hkc.1.1
        have hiv : Step.inValP (run bytes len i).st = false := by rw [hkey]; decide
        have hv : (signals (run bytes len i) (bytes i) r'.st).vEmit = false := by
          by_cases hv0 : (signals (run bytes len i) (bytes i) r'.st).vEmit = true
          case neg => simpa using hv0
          exfalso
          rcases vEmit_states hv0 with h1 | h1 | h1 | h1 <;> rw [hkey] at h1 <;>
            exact absurd h1 (by decide)
        left
        refine ⟨?_, Or.inl hzero⟩
        rw [hofsEq, hv, hiv, hzero]
        simp

/-! ### Consequences: the routed cells of a claim

The offsets of the emitting positions of claim `k` run through `0, …, slotLen - 1`
without repetition, so every cell below the slot length is written exactly once,
every cell at or above it is untouched, and the slot length fits the claim's cap. -/

theorem emitCount_le_succ (i : ℕ) :
    emitCount bytes len k i ≤ emitCount bytes len k (i + 1) := by
  rw [emitCount_succ]; omega

theorem emitCount_mono : ∀ {i j : ℕ}, i ≤ j →
    emitCount bytes len k i ≤ emitCount bytes len k j := by
  intro i j h
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h1 | h1
    · exact le_trans (ih (by omega)) (emitCount_le_succ bytes len k j)
    · have : i = j + 1 := by omega
      subst this; exact le_refl _

theorem emitCount_lt {a b : ℕ} (hab : a < b) (he : emitsAt bytes len k a = true) :
    emitCount bytes len k a < emitCount bytes len k b := by
  have h1 : emitCount bytes len k (a + 1) = emitCount bytes len k a + 1 := by
    rw [emitCount_succ, if_pos he]
  have h2 := emitCount_mono bytes len k (show a + 1 ≤ b by omega)
  omega

/-- A counting fact about `List.filter`: every count below the total is reached. -/
theorem exists_count (p : ℕ → Bool) : ∀ (N t : ℕ), t < ((List.range N).filter p).length →
    ∃ i, i < N ∧ p i = true ∧ ((List.range i).filter p).length = t := by
  intro N
  induction N with
  | zero => intro t ht; simp at ht
  | succ N ih =>
    intro t ht
    have hsucc : ((List.range (N + 1)).filter p).length
        = ((List.range N).filter p).length + (if p N = true then 1 else 0) := by
      simp only [List.range_succ, List.filter_append, List.length_append, List.filter_cons,
        List.filter_nil]
      by_cases h : p N = true <;> simp [h]
    rw [hsucc] at ht
    by_cases h : t < ((List.range N).filter p).length
    · obtain ⟨i, hi, hpi, hci⟩ := ih t h
      exact ⟨i, by omega, hpi, hci⟩
    · have hpN : p N = true := by
        by_cases hp : p N = true
        · exact hp
        · rw [if_neg hp] at ht; omega
      refine ⟨N, by omega, hpN, ?_⟩
      rw [if_pos hpN] at ht
      omega

/-! ### Bounds on the read-outs

Every routed value is a code point or a decimal digit, so it is far below the
field characteristic, and every count is bounded by the parsed length. -/

theorem valOut_lt {r : Regs} {b : ℕ} {st' : St} (hb : b < 256) (hh : r.hexAcc < 4096) :
    (signals r b st').valOut < 65536 := by
  rw [Step.sig_valOut]
  split
  · exact Step.sig_cp_lt r hb hh st'
  · split <;> omega

theorem runSignals_valOut_lt {i : ℕ} (hb : ∀ j, bytes j < 256) :
    (runSignals bytes len i).valOut < 65536 := by
  by_cases hi : i < len
  · rw [show runSignals bytes len i
        = signals (run bytes len i) (bytes i)
            ((step (run bytes len i) (bytes i)).getD (run bytes len i)).st from by
      simp only [runSignals, if_pos hi]]
    exact valOut_lt (hb i) (IR.run_hexAcc_lt bytes len i)
  · simp [runSignals, hi]

theorem presentCount_le : presentCount bytes len k ≤ len := by
  have := List.length_filter_le (fun i => (runSignals bytes len i).match_[k]) (List.range len)
  rw [List.length_range] at this
  exact this

theorem slotLen_le : slotLen bytes len k ≤ len := by
  have := List.length_filter_le
    (fun i => (runSignals bytes len i).vEmit && decide ((run bytes len i).claim = some k))
    (List.range len)
  rw [List.length_range] at this
  exact this

theorem signCount_le : signCount bytes len k ≤ len := by
  have := List.length_filter_le
    (fun i => (runSignals bytes len i).minusFlag && decide ((run bytes len i).claim = some k))
    (List.range len)
  rw [List.length_range] at this
  exact this

theorem trueCount_le : trueCount bytes len k ≤ len := by
  have := List.length_filter_le
    (fun i => (runSignals bytes len i).trueDone && decide ((run bytes len i).claim = some k))
    (List.range len)
  rw [List.length_range] at this
  exact this

/-- `Model.cell` with its `let`s expanded. -/
theorem cell_def (t : ℕ) :
    cell bytes len k t = ((List.range len).find? (fun i =>
      ((runSignals bytes len i).write && decide ((run bytes len i).claim = some k))
        && decide ((run bytes len i).ofs = t))).elim 0
        fun i => (runSignals bytes len i).valOut := rfl

theorem cell_lt (t : ℕ) (hb : ∀ j, bytes j < 256) : cell bytes len k t < 65536 := by
  rw [cell_def]
  cases hf : (List.range len).find? (fun i =>
      ((runSignals bytes len i).write && decide ((run bytes len i).claim = some k))
        && decide ((run bytes len i).ofs = t)) with
  | none => simp
  | some j => exact runSignals_valOut_lt bytes len hb

section Facts

variable (hkind : isStrClaim k = true ∨ isIntClaim k = true)
  (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
  (hpresent : presentCount bytes len k ≤ 1)

include hkind hsteps hpresent

/-- The offset of an emitting position is the number of values already routed. -/
theorem ofs_eq_emitCount {i : ℕ} (hi : i < len) (he : emitsAt bytes len k i = true) :
    (run bytes len i).ofs = emitCount bytes len k i :=
  (cinv bytes len k hkind hsteps hpresent len le_rfl).1 i hi he

/-- Two emitting positions with the same offset coincide. -/
theorem emits_inj {a c : ℕ} (ha : a < len) (hc : c < len)
    (hea : emitsAt bytes len k a = true) (hec : emitsAt bytes len k c = true)
    (hofs : (run bytes len a).ofs = (run bytes len c).ofs) : a = c := by
  rw [ofs_eq_emitCount bytes len k hkind hsteps hpresent ha hea,
    ofs_eq_emitCount bytes len k hkind hsteps hpresent hc hec] at hofs
  rcases Nat.lt_trichotomy a c with h | h | h
  · exact absurd hofs (Nat.ne_of_lt (emitCount_lt bytes len k h hea))
  · exact h
  · exact absurd hofs.symm (Nat.ne_of_lt (emitCount_lt bytes len k h hec))

/-- Every cell below the slot length is written. -/
theorem cover {t : ℕ} (ht : t < slotLen bytes len k) :
    ∃ i, i < len ∧ emitsAt bytes len k i = true ∧ (run bytes len i).ofs = t := by
  rw [slotLen_eq] at ht
  obtain ⟨i, hi, hpi, hci⟩ := exists_count (emitsAt bytes len k) len t ht
  refine ⟨i, hi, hpi, ?_⟩
  rw [ofs_eq_emitCount bytes len k hkind hsteps hpresent hi hpi]
  exact hci

/-- The slot length never exceeds the claim's cap: the routing row of the last
emitting position asks for `ofs < claimCap k`. -/
theorem slotLen_le_claimCap : slotLen bytes len k ≤ claimCap k := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨i, hi, hei, hofs⟩ := cover bytes len k hkind hsteps hpresent hlt
  obtain ⟨r', hs⟩ := Option.isSome_iff_exists.mp (hsteps i hi)
  have hsg : runSignals bytes len i = signals (run bytes len i) (bytes i) r'.st :=
    runSignals_pos bytes len hi hs
  simp only [emitsAt, Bool.and_eq_true, decide_eq_true_eq] at hei
  obtain ⟨hv, hcl⟩ := hei
  rw [hsg] at hv
  have hwr := write_of_emits k hkind hcl hv
  have := Step.step_capOk hs hwr k hcl
  omega

/-- No position writes a cell at or past the slot length. -/
theorem cell_eq_zero {t : ℕ} (ht : slotLen bytes len k ≤ t) : cell bytes len k t = 0 := by
  rw [cell_def]
  have hnone : ((List.range len).find? (fun i =>
      ((runSignals bytes len i).write && decide ((run bytes len i).claim = some k))
        && decide ((run bytes len i).ofs = t))) = none := by
    rw [List.find?_eq_none]
    intro j hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    rintro ⟨hw, hcl⟩ hofs
    exfalso
    have hjlt : j < len := List.mem_range.mp hj
    have hej : emitsAt bytes len k j = true := by
      simp only [emitsAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by rw [← write_eq_vEmit bytes len k hkind hcl]; exact hw, hcl⟩
    have h1 := ofs_eq_emitCount bytes len k hkind hsteps hpresent hjlt hej
    have h2 := emitCount_lt bytes len k hjlt hej
    rw [slotLen_eq] at ht
    omega
  rw [hnone]
  rfl

/-- The cell an emitting position writes holds that position's routed value. -/
theorem cell_eq_valOut {i : ℕ} (hi : i < len) (hei : emitsAt bytes len k i = true) :
    cell bytes len k ((run bytes len i).ofs) = (runSignals bytes len i).valOut := by
  rw [cell_def]
  set t := (run bytes len i).ofs with ht
  set q : ℕ → Bool := fun j =>
    ((runSignals bytes len j).write && decide ((run bytes len j).claim = some k))
      && decide ((run bytes len j).ofs = t) with hq_def
  have hq : ∀ j, q j = true ↔ (emitsAt bytes len k j = true ∧ (run bytes len j).ofs = t) := by
    intro j
    simp only [hq_def, emitsAt, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hw, hcl⟩, ho⟩
      exact ⟨⟨by rw [← write_eq_vEmit bytes len k hkind hcl]; exact hw, hcl⟩, ho⟩
    · rintro ⟨⟨hv, hcl⟩, ho⟩
      exact ⟨⟨by rw [write_eq_vEmit bytes len k hkind hcl]; exact hv, hcl⟩, ho⟩
  have hself : q i = true := (hq i).mpr ⟨hei, rfl⟩
  cases hf : (List.range len).find? q with
  | none =>
    exact absurd hself (List.find?_eq_none.mp hf i (List.mem_range.mpr hi))
  | some j =>
    have hqj := (hq j).mp (List.find?_some hf)
    have hjlt : j < len := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    have hji : j = i := emits_inj bytes len k hkind hsteps hpresent hjlt hi hqj.1 hei
      (by rw [hqj.2])
    rw [hji]
    rfl

end Facts

end Counting

end RunTheory
end Solution.JSONExtract
