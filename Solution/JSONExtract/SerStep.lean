import Solution.JSONExtract.RunList
import Solution.JSONExtract.Serial

/-!
# One step of the automaton, per transition (`JSONExtract`)

The forward direction of the grammar argument needs, for every transition the
serialization takes, the *exact* successor register record.  `mkNext` is that
record and `step_eq` computes `Model.step` with it; the rest of the file
specialises it to the concrete (state, byte class) pairs of the grammar.
-/

namespace Solution.JSONExtract

open Model (St Sub Claim Regs Kind nClaims kIdxMax ofsMax)

namespace SerStep

open Model
open Specs.JSON (quote backslash slash lbrace rbrace colon comma minus plus dot
  digit0 digit9 lowerA lowerB lowerE lowerF lowerN lowerR lowerT lowerU upperA upperE upperF
  space tab lf cr backspace formfeed trueLit falseLit nullLit)

/-- The successor register record of a step that is not rejected. -/
def mkNext (r : Regs) (b : ℕ) (sub' : Sub) (st' : St) : Regs :=
  { st := st', sub := sub',
    hexAcc := if r.sub = Sub.H1 ∨ r.sub = Sub.H2 ∨ r.sub = Sub.H3 then
        16 * r.hexAcc + hexVal b else 0,
    kIdx := if r.st = St.KEY then
        min (r.kIdx + (if (signals r b st').emit then 1 else 0)) (kIdxMax - 1) else 0,
    m := Vector.ofFn fun k : Claim =>
      if (signals r b st').keyStart then true
      else if r.st = St.KEY then
        r.m[k] && (!(signals r b st').emit || decide ((signals r b st').cp = nameAt k r.kIdx))
      else false,
    claim := if (signals r b st').keyClose then
        (List.finRange nClaims).find? (fun k => (signals r b st').match_[k])
      else if (signals r b st').keyStart then none else r.claim,
    ofs := min ((if Step.inValP r.st then r.ofs else 0)
      + (if (signals r b st').vEmit then 1 else 0)) (ofsMax - 1),
    nMem := r.nMem + (if (signals r b st').keyStart then 1 else 0) }

/-- The successor of a successful step is `mkNext` of its own sub- and main state. -/
theorem step_eq_mkNext {r r' : Regs} {b : ℕ} (h : step r b = some r') :
    r' = mkNext r b r'.sub r'.st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Step.step_fields h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := r'
  simp only at h3 h4 h5 h6 h7 h8 ⊢
  simp only [mkNext, Regs.mk.injEq]
  and_intros <;>
    first
      | trivial
      | (rw [h3]; simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc])
      | exact h4 | exact h5 | exact h6 | exact h7
      | (refine Vector.ext fun i hi => ?_
         rw [Vector.getElem_ofFn]
         exact h8 ⟨i, hi⟩)

theorem step_eq {r : Regs} {b : ℕ} {sub' : Sub} {st' : St}
    (hsub : stepSub (inStr r.st) r.sub b = some sub')
    (hst : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b = some st')
    (hcap : (signals r b st').write = true → ∀ k : Claim, r.claim = some k → r.ofs < claimCap k)
    (hascii : (signals r b st').write = true → r.st = St.STR → (signals r b st').cp < 0x80) :
    step r b = some (mkNext r b sub' st') := by
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (Step.step_isSome_of hsub hst hcap hascii)
  rw [hr']
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Step.step_fields hr'
  have hsub' : r'.sub = sub' := by rw [hsub] at h1; exact (Option.some.inj h1).symm
  have hst' : r'.st = st' := by rw [hst] at h2; exact (Option.some.inj h2).symm
  rw [hst'] at h4 h5 h6 h7 h8
  congr 1
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := r'
  simp only at hsub' hst' h3 h4 h5 h6 h7 h8
  subst hsub'; subst hst'
  simp only [mkNext, Regs.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | trivial
      | (rw [h3]; simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc])
      | exact h4 | exact h5 | exact h6 | exact h7
      | (refine Vector.ext fun i hi => ?_
         rw [Vector.getElem_ofFn]
         exact h8 ⟨i, hi⟩)

/-! ## Signal shorthands -/

theorem sig_keyStart (r : Regs) (b : ℕ) (st' : St) :
    (signals r b st').keyStart = (decide (st' = St.KEY) && decide (r.st ≠ St.KEY)) := rfl

theorem sig_emit_of_notInStr {r : Regs} {b : ℕ} {st' : St} (h : inStr r.st = false) :
    (signals r b st').emit = false := by
  simp [Step.sig_emit, Step.emitPlainB, Step.emitEscB, Step.emitUB, Step.emitUtf8B, h]

theorem sig_cp_of_notInStr {r : Regs} {b : ℕ} {st' : St} (h : inStr r.st = false) :
    (signals r b st').cp = 0 := by
  simp [Step.sig_cp, Step.emitPlainB, Step.emitEscB, Step.emitUB, Step.emitUtf8B, h]

theorem inStr_of_ne {s : St} (h1 : s ≠ St.KEY) (h2 : s ≠ St.STR) : inStr s = false := by
  simp [inStr, h1, h2]

theorem sig_vEmit_of {r : Regs} {b : ℕ} {st' : St} (h1 : inStr r.st = false)
    (h2 : Model.isDigit b = false ∨ (r.st ≠ St.PVAL ∧ r.st ≠ St.NSIGN ∧ r.st ≠ St.NINT)) :
    (signals r b st').vEmit = false := by
  rw [Step.sig_vEmit, Step.strEmitB, Step.digitEmitB, sig_emit_of_notInStr h1]
  rcases h2 with h | ⟨ha, hb, hc⟩
  · simp [h]
  · simp [ha, hb, hc]

theorem sig_write_of_vEmit {r : Regs} {b : ℕ} {st' : St} (h : (signals r b st').vEmit = false) :
    (signals r b st').write = false := by
  rw [Step.sig_write, ← Step.sig_vEmit r b st', h]; simp

/-! ## The normal register record of the whitespace states -/

/-- The register record at a state outside a key, a value and a string. -/
def normal (s : St) (c : Option Claim) (n : ℕ) : Regs :=
  { st := s, sub := Sub.PLAIN, hexAcc := 0, kIdx := 0, m := Vector.ofFn fun _ => false,
    claim := c, ofs := 0, nMem := n }

theorem init_eq_normal : Regs.init = normal St.PRE none 0 := by
  simp only [Regs.init, normal, Regs.mk.injEq]
  and_intros <;> first | trivial | (exact Vector.ext fun i hi => by simp)

/-- The states whose self-loop consumes whitespace. -/
def wsState (s : St) : Bool :=
  s == St.PRE || s == St.OBJ || s == St.AKEY || s == St.PVAL || s == St.AVAL || s == St.SEP ||
    s == St.END

theorem wsState_notInStr {s : St} (h : wsState s = true) : inStr s = false := by
  revert h; revert s; decide

theorem wsState_notInVal {s : St} (h : wsState s = true) : Step.inValP s = false := by
  revert h; revert s; decide

theorem wsState_ne_key {s : St} (h : wsState s = true) : s ≠ St.KEY := by
  revert h; revert s; decide

set_option maxHeartbeats 1000000 in
theorem stepSt_ws (kind : Kind) (sp : Bool) (s : St) (b : ℕ) (hs : wsState s = true)
    (hb : isWs b = true) : stepSt kind sp s b = some s := by
  revert hs
  fin_cases s <;>
    simp +decide only [wsState, stepSt, afterValue, St.PRE, St.OBJ, St.KEY, St.AKEY, St.PVAL,
      St.STR, St.NSIGN, St.NZERO, St.NINT, St.NDOT, St.NFRAC, St.NE, St.NESIGN, St.NEXP,
      St.T1, St.T2, St.T3, St.F1, St.F2, St.F3, St.F4, St.N1, St.N2, St.N3, St.AVAL, St.SEP,
      St.END, hb, beq_self_eq_true, Bool.or_true, Bool.true_or, if_true, if_false,
      forall_const, IsEmpty.forall_iff]

theorem stepSub_notInStr (sb : Sub) (b : ℕ) : stepSub false sb b = some Sub.PLAIN := rfl

theorem step_ws {r : Regs} {b : ℕ} (hb : isWs b = true) (hs : wsState r.st = true)
    (hsub : r.sub = Sub.PLAIN) :
    step r b = some (normal r.st r.claim r.nMem) := by
  have hnstr := wsState_notInStr hs
  have hnval := wsState_notInVal hs
  have hnkey := wsState_ne_key hs
  have h1 : stepSub (inStr r.st) r.sub b = some Sub.PLAIN := by
    rw [hnstr]; exact stepSub_notInStr _ _
  have h2 : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b = some r.st :=
    stepSt_ws _ _ _ _ hs hb
  have hve : (signals r b r.st).vEmit = false :=
    sig_vEmit_of hnstr (Or.inl (RunTheory.isWs_isDigit_false hb))
  have hw := sig_write_of_vEmit hve
  rw [step_eq h1 h2 (by rw [hw]; simp) (by rw [hw]; simp)]
  congr 1
  have hks : (signals r b r.st).keyStart = false := by
    rw [sig_keyStart]; simp [hnkey]
  have hkc : (signals r b r.st).keyClose = false := by
    rw [Step.sig_keyClose, Step.keyCloseB]; simp [hnkey]
  simp only [mkNext, normal, Regs.mk.injEq, hsub, hks, hkc, hve, hnval, hnkey]
  and_intros <;>
    first
      | trivial
      | (exact Vector.ext fun i hi => by simp)
      | simp [Sub.PLAIN, Sub.H1, Sub.H2, Sub.H3]

/-! ## Silent positions -/

open RunList (pMatch pEmit pMinus pTrue fVal runL traceL)

/-- No read-out signal fires at this position. -/
def Silent (x : Regs × ℕ) : Prop :=
  (∀ k : Claim, pMatch k x = false) ∧ (∀ k : Claim, pEmit k x = false) ∧
    (∀ k : Claim, pMinus k x = false) ∧ (∀ k : Claim, pTrue k x = false)

/-- No read-out signal fires anywhere in this trace. -/
def Quiet (T : List (Regs × ℕ)) : Prop := ∀ x ∈ T, Silent x

theorem quiet_nil : Quiet [] := by intro x hx; simp at hx

theorem quiet_append {T1 T2 : List (Regs × ℕ)} (h1 : Quiet T1) (h2 : Quiet T2) :
    Quiet (T1 ++ T2) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

theorem quiet_cons {x : Regs × ℕ} {T : List (Regs × ℕ)} (h1 : Silent x) (h2 : Quiet T) :
    Quiet (x :: T) := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | h
  · exact h1
  · exact h2 y h

theorem quiet_single {x : Regs × ℕ} (h : Silent x) : Quiet [x] := quiet_cons h quiet_nil

theorem silent_sig0 {r : Regs} {b : ℕ} (hk : ∀ k : Claim, (signals r b r.st).match_[k] = false)
    (hv : (signals r b r.st).vEmit = false) (hp : (signals r b r.st).minusFlag = false)
    (ht : (signals r b r.st).trueDone = false) : Silent (r, b) := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [pMatch]; simp [hk k]
  · rw [pEmit]; simp [hv]
  · rw [pMinus]; simp [hp]
  · rw [pTrue]; simp [ht]

theorem silent_sig {r : Regs} {b : ℕ} (hk : r.st ≠ St.KEY)
    (hv : (signals r b r.st).vEmit = false) (hp : (signals r b r.st).minusFlag = false)
    (ht : (signals r b r.st).trueDone = false) : Silent (r, b) := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [pMatch, Step.sig_match, Step.keyCloseB]; simp [hk]
  · rw [pEmit]; simp [hv]
  · rw [pMinus]; simp [hp]
  · rw [pTrue]; simp [ht]

theorem silent_of {r : Regs} {b : ℕ} (hk : r.st ≠ St.KEY)
    (hv : (signals r b r.st).vEmit = false) (hp : r.st ≠ St.PVAL) (ht : r.st ≠ St.T3) :
    Silent (r, b) :=
  silent_sig hk hv (by rw [Step.sig_minusFlag]; simp [hp]) (by rw [Step.sig_trueDone]; simp [ht])

/-! ## The coarse position invariant

Between the key and the value of a member only the main state, the sub-state,
the claim register and the member count matter: every step outside a key or a
value recomputes the other registers from scratch. -/

/-- The automaton sits at `s`, outside a string, reading claim `c`, having
started `n` members. -/
def AtS (s : St) (c : Option Claim) (n : ℕ) (r : Regs) : Prop :=
  r.st = s ∧ r.sub = Sub.PLAIN ∧ r.claim = c ∧ r.nMem = n

/-- The states a finished value can sit in. -/
def endValState (s : St) : Bool :=
  s == St.AVAL || s == St.NZERO || s == St.NINT || s == St.NFRAC || s == St.NEXP

/-- The automaton has just finished a value. -/
def AtE (c : Option Claim) (n : ℕ) (r : Regs) : Prop :=
  endValState r.st = true ∧ r.sub = Sub.PLAIN ∧ r.claim = c ∧ r.nMem = n

theorem endValState_notInStr {s : St} (h : endValState s = true) : inStr s = false := by
  revert h; revert s; decide

theorem endValState_ne_key {s : St} (h : endValState s = true) : s ≠ St.KEY := by
  revert h; revert s; decide

theorem endValState_ne_pval {s : St} (h : endValState s = true) : s ≠ St.PVAL := by
  revert h; revert s; decide

theorem endValState_ne_t3 {s : St} (h : endValState s = true) : s ≠ St.T3 := by
  revert h; revert s; decide

theorem endValState_aval : endValState St.AVAL = true := by decide

/-! ## Byte-class arithmetic -/

theorem isWs_not_digit {b : ℕ} (h : Model.isWs b = true) : Model.isDigit b = false :=
  RunTheory.isWs_isDigit_false h

theorem isWs_cases {b : ℕ} (h : Model.isWs b = true) :
    b = space ∨ b = tab ∨ b = lf ∨ b = cr := by
  simpa only [Model.isWs, Bool.or_eq_true, beq_iff_eq, or_assoc] using h

theorem isWs_ne_dot {b : ℕ} (h : Model.isWs b = true) : (b == dot) = false := by
  rcases isWs_cases h with rfl | rfl | rfl | rfl <;> decide

theorem isWs_not_exp {b : ℕ} (h : Model.isWs b = true) : Model.isExpLetter b = false := by
  rcases isWs_cases h with rfl | rfl | rfl | rfl <;> decide

theorem comma_not_digit : Model.isDigit comma = false := by decide
theorem comma_not_ws : Model.isWs comma = false := by decide
theorem comma_ne_dot : (comma == dot) = false := by decide
theorem comma_not_exp : Model.isExpLetter comma = false := by decide
theorem rbrace_not_digit : Model.isDigit rbrace = false := by decide
theorem rbrace_not_ws : Model.isWs rbrace = false := by decide
theorem rbrace_ne_dot : (rbrace == dot) = false := by decide
theorem rbrace_not_exp : Model.isExpLetter rbrace = false := by decide

set_option maxHeartbeats 1000000 in
/-- Out of a finished value every byte that is not a digit, a `.` or an
exponent letter goes through `afterValue`. -/
theorem stepSt_endVal (kind : Kind) (sp : Bool) (s : St) (b : ℕ) (hs : endValState s = true)
    (hnd : Model.isDigit b = false) (hdot : (b == dot) = false)
    (hexp : Model.isExpLetter b = false) : stepSt kind sp s b = afterValue b := by
  revert hs
  fin_cases s <;>
    simp +decide only [endValState, stepSt, St.PRE, St.OBJ, St.KEY, St.AKEY, St.PVAL,
      St.STR, St.NSIGN, St.NZERO, St.NINT, St.NDOT, St.NFRAC, St.NE, St.NESIGN, St.NEXP,
      St.T1, St.T2, St.T3, St.F1, St.F2, St.F3, St.F4, St.N1, St.N2, St.N3, St.AVAL, St.SEP,
      St.END, hnd, hdot, hexp, Bool.false_and, Bool.and_false, if_true, if_false,
      forall_const, IsEmpty.forall_iff, imp_self]

/-! ## The structural steps -/

theorem afterValue_ne_key {b : ℕ} {s' : St} (h : afterValue b = some s') : s' ≠ St.KEY := by
  rw [afterValue] at h
  split_ifs at h <;>
    first
      | (rw [← Option.some.inj h]; decide)
      | exact absurd h (by simp)

theorem step_of_AtE {c : Option Claim} {n : ℕ} {r : Regs} {b : ℕ} {s' : St}
    (h : AtE c n r) (hnd : Model.isDigit b = false) (hdot : (b == dot) = false)
    (hexp : Model.isExpLetter b = false) (hav : afterValue b = some s') :
    ∃ r', step r b = some r' ∧ r'.st = s' ∧ r'.sub = Sub.PLAIN ∧ r'.claim = c ∧
      r'.nMem = n ∧ Silent (r, b) := by
  obtain ⟨hs, hsub, hcl, hnm⟩ := h
  have hnstr := endValState_notInStr hs
  have h1 : stepSub (inStr r.st) r.sub b = some Sub.PLAIN := by
    rw [hnstr]; exact stepSub_notInStr _ _
  have h2 : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b = some s' := by
    rw [stepSt_endVal _ _ _ _ hs hnd hdot hexp]; exact hav
  have hve : (signals r b r.st).vEmit = false := sig_vEmit_of hnstr (Or.inl hnd)
  have hve' : (signals r b s').vEmit = false := by rw [← RunList.sig_vEmit_indep r b r.st s']; exact hve
  have hw := sig_write_of_vEmit hve'
  refine ⟨mkNext r b Sub.PLAIN s', step_eq h1 h2 (by rw [hw]; simp) (by rw [hw]; simp),
    rfl, rfl, ?_, ?_, silent_of (endValState_ne_key hs) hve (endValState_ne_pval hs)
      (endValState_ne_t3 hs)⟩
  · have hks : (signals r b s').keyStart = false := by
      rw [sig_keyStart]; simp [afterValue_ne_key hav]
    have hkc : (signals r b s').keyClose = false := by
      rw [Step.sig_keyClose, Step.keyCloseB]; simp [endValState_ne_key hs]
    simp only [mkNext, hks, hkc, if_false, Bool.false_eq_true]
    exact hcl
  · have hks : (signals r b s').keyStart = false := by
      rw [sig_keyStart]; simp [afterValue_ne_key hav]
    simp only [mkNext, hks, if_false, Bool.false_eq_true, add_zero]
    exact hnm

theorem step_endVal_ws {c : Option Claim} {n : ℕ} {r : Regs} {b : ℕ} (h : AtE c n r)
    (hb : Model.isWs b = true) :
    ∃ r', step r b = some r' ∧ AtE c n r' ∧ Silent (r, b) := by
  obtain ⟨r', hstep, hst, hsub, hcl, hnm, hsil⟩ :=
    step_of_AtE h (isWs_not_digit hb) (isWs_ne_dot hb) (isWs_not_exp hb)
      (show afterValue b = some St.AVAL by rw [afterValue, if_pos hb])
  exact ⟨r', hstep, ⟨by rw [hst]; exact endValState_aval, hsub, hcl, hnm⟩, hsil⟩

theorem step_endVal_comma {c : Option Claim} {n : ℕ} {r : Regs} (h : AtE c n r) :
    ∃ r', step r comma = some r' ∧ AtS St.SEP c n r' ∧ Silent (r, comma) := by
  obtain ⟨r', hstep, hst, hsub, hcl, hnm, hsil⟩ :=
    step_of_AtE h comma_not_digit comma_ne_dot comma_not_exp
      (show afterValue comma = some St.SEP by
        rw [afterValue, if_neg (by simp [comma_not_ws]), if_pos (by simp)])
  exact ⟨r', hstep, ⟨hst, hsub, hcl, hnm⟩, hsil⟩

theorem step_endVal_rbrace {c : Option Claim} {n : ℕ} {r : Regs} (h : AtE c n r) :
    ∃ r', step r rbrace = some r' ∧ AtS St.END c n r' ∧ Silent (r, rbrace) := by
  obtain ⟨r', hstep, hst, hsub, hcl, hnm, hsil⟩ :=
    step_of_AtE h rbrace_not_digit rbrace_ne_dot rbrace_not_exp
      (show afterValue rbrace = some St.END by
        rw [afterValue, if_neg (by simp [rbrace_not_ws]), if_neg (by decide), if_pos (by simp)])
  exact ⟨r', hstep, ⟨hst, hsub, hcl, hnm⟩, hsil⟩

/-! ## Whitespace runs -/

theorem normal_st (s : St) (c : Option Claim) (n : ℕ) : (normal s c n).st = s := rfl
theorem normal_sub (s : St) (c : Option Claim) (n : ℕ) : (normal s c n).sub = Sub.PLAIN := rfl
theorem normal_claim (s : St) (c : Option Claim) (n : ℕ) : (normal s c n).claim = c := rfl
theorem normal_nMem (s : St) (c : Option Claim) (n : ℕ) : (normal s c n).nMem = n := rfl
theorem normal_ofs (s : St) (c : Option Claim) (n : ℕ) : (normal s c n).ofs = 0 := rfl

theorem atS_normal (s : St) (c : Option Claim) (n : ℕ) : AtS s c n (normal s c n) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem isWs_ne_minus {b : ℕ} (h : Model.isWs b = true) : (b == minus) = false := by
  rcases isWs_cases h with rfl | rfl | rfl | rfl <;> decide

theorem isWs_ne_lowerE {b : ℕ} (h : Model.isWs b = true) : (b == lowerE) = false := by
  rcases isWs_cases h with rfl | rfl | rfl | rfl <;> decide

theorem silent_ws {r : Regs} {b : ℕ} (hs : wsState r.st = true) (hb : Model.isWs b = true) :
    Silent (r, b) :=
  silent_sig (wsState_ne_key hs)
    (sig_vEmit_of (wsState_notInStr hs) (Or.inl (isWs_not_digit hb)))
    (by rw [Step.sig_minusFlag, isWs_ne_minus hb]; simp)
    (by rw [Step.sig_trueDone, isWs_ne_lowerE hb]; simp)

/-- A whitespace run at a whitespace state, from the normal record. -/
theorem ws_run_normal {s : St} {c : Option Claim} {n : ℕ} {w : List ℕ}
    (hs : wsState s = true) (hw : Serial.IsWs w) :
    runL (normal s c n) w = some (normal s c n) ∧ Quiet (traceL (normal s c n) w) := by
  induction w with
  | nil => exact ⟨rfl, quiet_nil⟩
  | cons b w ih =>
    have hb : Model.isWs b = true := hw b (List.mem_cons_self ..)
    have hw' : Serial.IsWs w := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    have hstep : step (normal s c n) b = some (normal s c n) := by
      have := step_ws (r := normal s c n) hb (by rw [normal_st]; exact hs) (normal_sub s c n)
      rwa [normal_st, normal_claim, normal_nMem] at this
    obtain ⟨ih1, ih2⟩ := ih hw'
    refine ⟨by rw [RunList.runL_cons, hstep, Option.bind_some]; exact ih1, ?_⟩
    rw [RunList.traceL_cons_of_some hstep]
    exact quiet_cons (silent_ws (by rw [normal_st]; exact hs) hb) ih2

/-- A whitespace run at a whitespace state. -/
theorem ws_run_AtS {s : St} {c : Option Claim} {n : ℕ} {r : Regs} {w : List ℕ}
    (h : AtS s c n r) (hs : wsState s = true) (hw : Serial.IsWs w) :
    ∃ r', runL r w = some r' ∧ AtS s c n r' ∧ Quiet (traceL r w) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases w with
  | nil => exact ⟨r, rfl, ⟨h1, h2, h3, h4⟩, quiet_nil⟩
  | cons b w =>
    have hb : Model.isWs b = true := hw b (List.mem_cons_self ..)
    have hw' : Serial.IsWs w := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    have hstep : step r b = some (normal s c n) := by
      have := step_ws (r := r) hb (by rw [h1]; exact hs) h2
      rwa [h1, h3, h4] at this
    obtain ⟨ih1, ih2⟩ := ws_run_normal (s := s) (c := c) (n := n) hs hw'
    refine ⟨normal s c n, by rw [RunList.runL_cons, hstep, Option.bind_some]; exact ih1,
      atS_normal s c n, ?_⟩
    rw [RunList.traceL_cons_of_some hstep]
    exact quiet_cons (silent_ws (by rw [h1]; exact hs) hb) ih2

/-- A whitespace run just after a value. -/
theorem ws_run_AtE {c : Option Claim} {n : ℕ} {r : Regs} {w : List ℕ}
    (h : AtE c n r) (hw : Serial.IsWs w) :
    ∃ r', runL r w = some r' ∧ AtE c n r' ∧ Quiet (traceL r w) := by
  induction w generalizing r with
  | nil => exact ⟨r, rfl, h, quiet_nil⟩
  | cons b w ih =>
    have hb : Model.isWs b = true := hw b (List.mem_cons_self ..)
    have hw' : Serial.IsWs w := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    obtain ⟨r1, hstep, h1, hsil⟩ := step_endVal_ws h hb
    obtain ⟨r2, hrun, h2, hq⟩ := ih h1 hw'
    refine ⟨r2, by rw [RunList.runL_cons, hstep, Option.bind_some]; exact hrun, h2, ?_⟩
    rw [RunList.traceL_cons_of_some hstep]
    exact quiet_cons hsil hq

/-! ## The structural steps outside values -/

/-- A step outside a string, a key and a value, into a state that is not `KEY`:
the successor record is the normal record of the target state. -/
theorem step_struct {s : St} {c : Option Claim} {n : ℕ} {r : Regs} {b : ℕ} {s' : St}
    (h : AtS s c n r) (hnstr : inStr s = false) (hnval : Step.inValP s = false)
    (hnk : s ≠ St.KEY) (hs'k : s' ≠ St.KEY) (hnd : Model.isDigit b = false)
    (hst : stepSt (kindOf c) true s b = some s') :
    step r b = some (normal s' c n) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : stepSub (inStr r.st) r.sub b = some Sub.PLAIN := by
    rw [h1, hnstr]; exact stepSub_notInStr _ _
  have e2 : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b = some s' := by
    rw [h1, h2, h3]; simpa using hst
  have hve : (signals r b s').vEmit = false := by
    rw [← RunList.sig_vEmit_indep r b r.st s']
    exact sig_vEmit_of (by rw [h1]; exact hnstr) (Or.inl hnd)
  have hw := sig_write_of_vEmit hve
  rw [step_eq e1 e2 (by rw [hw]; simp) (by rw [hw]; simp)]
  congr 1
  have hks : (signals r b s').keyStart = false := by rw [sig_keyStart]; simp [hs'k]
  have hkc : (signals r b s').keyClose = false := by
    rw [Step.sig_keyClose, Step.keyCloseB]; simp [h1, hnk]
  simp only [mkNext, normal, Regs.mk.injEq, h1, h2, h3, h4, hks, hkc, hve, hnval, hnk]
  and_intros <;>
    first
      | trivial
      | (exact Vector.ext fun i hi => by simp)
      | simp [Sub.PLAIN, Sub.H1, Sub.H2, Sub.H3]

/-! ## Concrete main-automaton edges -/

theorem stepSt_pre_lbrace (kind : Kind) (sp : Bool) :
    stepSt kind sp St.PRE lbrace = some St.OBJ := by
  simp +decide [stepSt, St.PRE, St.OBJ, Model.isWs]

theorem stepSt_obj_rbrace (kind : Kind) (sp : Bool) :
    stepSt kind sp St.OBJ rbrace = some St.END := by
  simp +decide [stepSt, St.PRE, St.OBJ, St.END, Model.isWs]

theorem stepSt_obj_quote (kind : Kind) (sp : Bool) :
    stepSt kind sp St.OBJ quote = some St.KEY := by
  simp +decide [stepSt, St.PRE, St.OBJ, St.KEY, Model.isWs]

theorem stepSt_sep_quote (kind : Kind) (sp : Bool) :
    stepSt kind sp St.SEP quote = some St.KEY := by
  simp +decide [stepSt, St.PRE, St.OBJ, St.KEY, St.AKEY, St.PVAL, St.STR, St.NSIGN, St.NZERO,
    St.NINT, St.NDOT, St.NFRAC, St.NE, St.NESIGN, St.NEXP, St.T1, St.T2, St.T3, St.F1, St.F2,
    St.F3, St.F4, St.N1, St.N2, St.N3, St.AVAL, St.SEP, St.END, Model.isWs]

theorem stepSt_akey_colon (kind : Kind) (sp : Bool) :
    stepSt kind sp St.AKEY colon = some St.PVAL := by
  simp +decide [stepSt, St.PRE, St.OBJ, St.KEY, St.AKEY, St.PVAL, Model.isWs]

theorem stepSt_key_quote (kind : Kind) :
    stepSt kind true St.KEY quote = some St.AKEY := by
  simp +decide [stepSt, St.PRE, St.OBJ, St.KEY, St.AKEY]

/-! ## Contributions of a trace -/

def cMatch (k : Claim) (T : List (Regs × ℕ)) : ℕ := (T.filter (pMatch k)).length
def cSign (k : Claim) (T : List (Regs × ℕ)) : ℕ := (T.filter (pMinus k)).length
def cTrue (k : Claim) (T : List (Regs × ℕ)) : ℕ := (T.filter (pTrue k)).length

open RunList (valsT)

@[simp] theorem cMatch_nil (k : Claim) : cMatch k [] = 0 := rfl
@[simp] theorem cSign_nil (k : Claim) : cSign k [] = 0 := rfl
@[simp] theorem cTrue_nil (k : Claim) : cTrue k [] = 0 := rfl
@[simp] theorem valsT_nil (k : Claim) : valsT k [] = [] := rfl

theorem cMatch_append (k : Claim) (T1 T2 : List (Regs × ℕ)) :
    cMatch k (T1 ++ T2) = cMatch k T1 + cMatch k T2 := by simp [cMatch]
theorem cSign_append (k : Claim) (T1 T2 : List (Regs × ℕ)) :
    cSign k (T1 ++ T2) = cSign k T1 + cSign k T2 := by simp [cSign]
theorem cTrue_append (k : Claim) (T1 T2 : List (Regs × ℕ)) :
    cTrue k (T1 ++ T2) = cTrue k T1 + cTrue k T2 := by simp [cTrue]
theorem valsT_append (k : Claim) (T1 T2 : List (Regs × ℕ)) :
    valsT k (T1 ++ T2) = valsT k T1 ++ valsT k T2 := by simp [valsT]

theorem cMatch_cons (k : Claim) (x : Regs × ℕ) (T : List (Regs × ℕ)) :
    cMatch k (x :: T) = (if pMatch k x = true then 1 else 0) + cMatch k T := by
  by_cases h : pMatch k x = true <;> simp [cMatch, h] <;> omega
theorem cSign_cons (k : Claim) (x : Regs × ℕ) (T : List (Regs × ℕ)) :
    cSign k (x :: T) = (if pMinus k x = true then 1 else 0) + cSign k T := by
  by_cases h : pMinus k x = true <;> simp [cSign, h] <;> omega
theorem cTrue_cons (k : Claim) (x : Regs × ℕ) (T : List (Regs × ℕ)) :
    cTrue k (x :: T) = (if pTrue k x = true then 1 else 0) + cTrue k T := by
  by_cases h : pTrue k x = true <;> simp [cTrue, h] <;> omega
theorem valsT_cons (k : Claim) (x : Regs × ℕ) (T : List (Regs × ℕ)) :
    valsT k (x :: T) = (if pEmit k x = true then [fVal x] else []) ++ valsT k T := by
  by_cases h : pEmit k x = true <;> simp [valsT, h]

theorem cMatch_of_quiet {T : List (Regs × ℕ)} (h : Quiet T) (k : Claim) : cMatch k T = 0 := by
  rw [cMatch, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx
  simp [(h x hx).1 k]

theorem cSign_of_quiet {T : List (Regs × ℕ)} (h : Quiet T) (k : Claim) : cSign k T = 0 := by
  rw [cSign, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx
  simp [(h x hx).2.2.1 k]

theorem cTrue_of_quiet {T : List (Regs × ℕ)} (h : Quiet T) (k : Claim) : cTrue k T = 0 := by
  rw [cTrue, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx
  simp [(h x hx).2.2.2 k]

theorem valsT_of_quiet {T : List (Regs × ℕ)} (h : Quiet T) (k : Claim) : valsT k T = [] := by
  rw [valsT, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx
  simp [(h x hx).2.1 k]

/-! ## Inside a string body

Inside a key or a string value only the sub-state and the hex accumulator
decide whether a code point is emitted and which one. -/

/-- The emission flag inside a string. -/
def emitB (sb : Sub) (b : ℕ) : Bool :=
  (decide (sb = Sub.PLAIN) && Model.isUnescaped b) ||
    (decide (sb = Sub.ESC) && Model.isSimpleEsc b) ||
    (decide (sb = Sub.H4) && Model.isHex b) || (decide (sb = Sub.C1) && Model.isCont b)

/-- The emitted code point inside a string. -/
def cpB (sb : Sub) (h b : ℕ) : ℕ :=
  if decide (sb = Sub.PLAIN) && Model.isUnescaped b then b
  else if decide (sb = Sub.ESC) && Model.isSimpleEsc b then Model.escVal b
  else if decide (sb = Sub.H4) && Model.isHex b then 16 * h + Model.hexVal b
  else if decide (sb = Sub.C1) && Model.isCont b then Model.nonAsciiMarker else 0

theorem sig_emit_inStr {r : Regs} {b : ℕ} {st' : St} (h : inStr r.st = true) :
    (signals r b st').emit = emitB r.sub b := by
  rw [Step.sig_emit, Step.emitPlainB, Step.emitEscB, Step.emitUB, Step.emitUtf8B, h, emitB]
  simp

theorem sig_cp_inStr {r : Regs} {b : ℕ} {st' : St} (h : inStr r.st = true) :
    (signals r b st').cp = cpB r.sub r.hexAcc b := by
  rw [Step.sig_cp, Step.emitPlainB, Step.emitEscB, Step.emitUB, Step.emitUtf8B, h, cpB]
  simp

/-! ## The sub-automaton, edge by edge -/

theorem stepSub_plain_unesc {b : ℕ} (h : Model.isUnescaped b = true) :
    stepSub true Sub.PLAIN b = some Sub.PLAIN := by
  simp [stepSub, Sub.PLAIN, h]

theorem stepSub_plain_quote : stepSub true Sub.PLAIN quote = some Sub.PLAIN := by
  simp +decide [stepSub, Sub.PLAIN]

theorem stepSub_plain_bslash : stepSub true Sub.PLAIN backslash = some Sub.ESC := by
  simp +decide [stepSub, Sub.PLAIN, Sub.ESC, Model.isUnescaped]

theorem stepSub_esc_simple {b : ℕ} (h : Model.isSimpleEsc b = true) :
    stepSub true Sub.ESC b = some Sub.PLAIN := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, h]

theorem stepSub_esc_u : stepSub true Sub.ESC lowerU = some Sub.H1 := by
  simp +decide [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Model.isSimpleEsc]

theorem stepSub_h1 {b : ℕ} (h : Model.isHex b = true) : stepSub true Sub.H1 b = some Sub.H2 := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, h]

theorem stepSub_h2 {b : ℕ} (h : Model.isHex b = true) : stepSub true Sub.H2 b = some Sub.H3 := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, h]

theorem stepSub_h3 {b : ℕ} (h : Model.isHex b = true) : stepSub true Sub.H3 b = some Sub.H4 := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, Sub.H4, h]

theorem stepSub_h4 {b : ℕ} (h : Model.isHex b = true) :
    stepSub true Sub.H4 b = some Sub.PLAIN := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, Sub.H4, h]

theorem stepSub_c1 {b : ℕ} (h : Model.isCont b = true) :
    stepSub true Sub.C1 b = some Sub.PLAIN := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, Sub.H4, Sub.C1, h]

theorem stepSub_c2 {b : ℕ} (h : Model.isCont b = true) : stepSub true Sub.C2 b = some Sub.C1 := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, Sub.H4, Sub.C1, Sub.C2, h]

theorem stepSub_c3 {b : ℕ} (h : Model.isCont b = true) : stepSub true Sub.C3 b = some Sub.C2 := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, Sub.H4, Sub.C1, Sub.C2, Sub.C3, h]

theorem stepSub_e0s {b : ℕ} (h : Model.isContA0BF b = true) :
    stepSub true Sub.E0s b = some Sub.C1 := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, Sub.H4, Sub.C1, Sub.C2, Sub.C3,
    Sub.E0s, h]

theorem stepSub_eds {b : ℕ} (h : Model.isCont809F b = true) :
    stepSub true Sub.EDs b = some Sub.C1 := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, Sub.H4, Sub.C1, Sub.C2, Sub.C3,
    Sub.E0s, Sub.EDs, h]

theorem stepSub_f0s {b : ℕ} (h : Model.isCont90BF b = true) :
    stepSub true Sub.F0s b = some Sub.C2 := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, Sub.H4, Sub.C1, Sub.C2, Sub.C3,
    Sub.E0s, Sub.EDs, Sub.F0s, h]

theorem stepSub_f4s {b : ℕ} (h : Model.isCont808F b = true) :
    stepSub true Sub.F4s b = some Sub.C2 := by
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H2, Sub.H3, Sub.H4, Sub.C1, Sub.C2, Sub.C3,
    Sub.E0s, Sub.EDs, Sub.F0s, Sub.F4s, h]

theorem stepSub_plain_lead2 {b : ℕ} (h : Model.isLead2 b = true) :
    stepSub true Sub.PLAIN b = some Sub.C1 := by
  have h1 : (b == quote) = false := by
    simp only [Model.isLead2, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [beq_eq_false_iff_ne, ne_eq]
    show b ≠ 0x22
    omega
  have h2 : Model.isUnescaped b = false := by
    simp only [Model.isLead2, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Model.isUnescaped, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
    omega
  have h3 : (b == backslash) = false := by
    simp only [Model.isLead2, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [beq_eq_false_iff_ne, ne_eq]
    show b ≠ 0x5C
    omega
  simp [stepSub, Sub.PLAIN, Sub.ESC, Sub.C1, h, h1, h2, h3]

theorem stepSub_plain_high {b : ℕ} (hb : 0x80 ≤ b) :
    stepSub true Sub.PLAIN b =
      (if Model.isLead2 b = true then some Sub.C1 else if (b == 0xE0) = true then some Sub.E0s
       else if Model.isLead3 b = true then some Sub.C2 else if (b == 0xED) = true then some Sub.EDs
       else if (b == 0xF0) = true then some Sub.F0s else if Model.isLead4 b = true then some Sub.C3
       else if (b == 0xF4) = true then some Sub.F4s else none) := by
  have h1 : (b == quote) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x22; omega
  have h2 : Model.isUnescaped b = false := by
    simp only [Model.isUnescaped, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
    left; left; right; show 0x7F < b; omega
  have h3 : (b == backslash) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x5C; omega
  simp [stepSub, Sub.PLAIN, h1, h2, h3]

theorem stepSub_plain_e0 : stepSub true Sub.PLAIN 0xE0 = some Sub.E0s := by
  rw [stepSub_plain_high (by norm_num)]; decide

theorem stepSub_plain_lead3 {b : ℕ} (h : Model.isLead3 b = true) :
    stepSub true Sub.PLAIN b = some Sub.C2 := by
  have hb : 0x80 ≤ b := by
    simp only [Model.isLead3, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h; omega
  have h2 : Model.isLead2 b = false := by
    simp only [Model.isLead3, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Model.isLead2, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]; omega
  have h3 : (b == 0xE0) = false := by
    simp only [Model.isLead3, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [beq_eq_false_iff_ne, ne_eq]; omega
  rw [stepSub_plain_high hb, if_neg (by simp [h2]), if_neg (by simp [h3]), if_pos (by simp [h])]

theorem stepSub_plain_ed : stepSub true Sub.PLAIN 0xED = some Sub.EDs := by
  rw [stepSub_plain_high (by norm_num)]; decide

theorem stepSub_plain_f0 : stepSub true Sub.PLAIN 0xF0 = some Sub.F0s := by
  rw [stepSub_plain_high (by norm_num)]; decide

theorem stepSub_plain_lead4 {b : ℕ} (h : Model.isLead4 b = true) :
    stepSub true Sub.PLAIN b = some Sub.C3 := by
  have hh : 0xF1 ≤ b ∧ b ≤ 0xF3 := by
    simpa only [Model.isLead4, Bool.and_eq_true, decide_eq_true_eq] using h
  have hb : 0x80 ≤ b := by omega
  have h2 : Model.isLead2 b = false := by
    simp only [Model.isLead2, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]; omega
  have h3 : (b == 0xE0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have h4 : Model.isLead3 b = false := by
    simp only [Model.isLead3, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, not_le]
    constructor <;> [skip; skip] <;> omega
  have h5 : (b == 0xED) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have h6 : (b == 0xF0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  rw [stepSub_plain_high hb, if_neg (by simp [h2]), if_neg (by simp [h3]), if_neg (by simp [h4]),
    if_neg (by simp [h5]), if_neg (by simp [h6]), if_pos (by simp [h])]

theorem stepSub_plain_f4 : stepSub true Sub.PLAIN 0xF4 = some Sub.F4s := by
  rw [stepSub_plain_high (by norm_num)]; decide

/-! ## Stepping inside a key and inside a string value -/

/-- The register record inside a key. -/
def kRegs (sb : Sub) (h i : ℕ) (mv : Vector Bool nClaims) (n : ℕ) : Regs :=
  { st := St.KEY, sub := sb, hexAcc := h, kIdx := i, m := mv, claim := none, ofs := 0, nMem := n }

/-- The register record inside a string value. -/
def sRegs (sb : Sub) (h : ℕ) (c : Option Claim) (o n : ℕ) : Regs :=
  { st := St.STR, sub := sb, hexAcc := h, kIdx := 0, m := Vector.ofFn fun _ => false,
    claim := c, ofs := o, nMem := n }

private theorem hexAcc_next (sb : Sub) (h b : ℕ) :
    (if (decide (sb = Sub.H1) || decide (sb = Sub.H2) || decide (sb = Sub.H3)) = true then
        16 * h + Model.hexVal b else 0)
      = if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * h + Model.hexVal b else 0 := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc]

theorem stepSt_key_stay (kind : Kind) (sp : Bool) {b : ℕ} (hq : ((b == quote) && sp) = false) :
    stepSt kind sp St.KEY b = some St.KEY := by
  have e : stepSt kind sp St.KEY b =
      if ((b == quote) && sp) = true then some St.AKEY else some St.KEY := rfl
  rw [e, if_neg (by simp [hq])]

theorem stepSt_str_stay (kind : Kind) (sp : Bool) {b : ℕ} (hq : ((b == quote) && sp) = false) :
    stepSt kind sp St.STR b = some St.STR := by
  have e : stepSt kind sp St.STR b =
      if ((b == quote) && sp) = true then some St.AVAL else some St.STR := rfl
  rw [e, if_neg (by simp [hq])]

theorem step_kRegs {sb sb' : Sub} {h i n : ℕ} {mv : Vector Bool nClaims} {b : ℕ}
    (hsub : stepSub true sb b = some sb')
    (hq : ((b == quote) && decide (sb = Sub.PLAIN)) = false) :
    step (kRegs sb h i mv n) b = some (kRegs sb'
      (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * h + Model.hexVal b else 0)
      (min (i + (if emitB sb b then 1 else 0)) (kIdxMax - 1))
      (Vector.ofFn fun k : Claim =>
        mv[k] && (!emitB sb b || decide (cpB sb h b = nameAt k i))) n) ∧
    Silent (kRegs sb h i mv n, b) := by
  set r : Regs := kRegs sb h i mv n with hr
  have hstK : r.st = St.KEY := rfl
  have hsubr : r.sub = sb := rfl
  have hstr : inStr r.st = true := by rw [hstK]; rfl
  have e1 : stepSub (inStr r.st) r.sub b = some sb' := by rw [hstr, hsubr]; exact hsub
  have e2 : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b = some St.KEY := by
    rw [hstK, hsubr]; exact stepSt_key_stay _ _ hq
  have hve : (signals r b St.KEY).vEmit = false := by
    rw [Step.sig_vEmit, Step.strEmitB, Step.digitEmitB, hstK]; simp [St.KEY, St.STR, St.PVAL,
      St.NSIGN, St.NINT]
  have hw := sig_write_of_vEmit hve
  have hkc : (signals r b St.KEY).keyClose = false := by
    rw [Step.sig_keyClose, Step.keyCloseB, hstK, hsubr]; simpa using hq
  have hks : (signals r b St.KEY).keyStart = false := by
    rw [sig_keyStart, hstK]; simp
  have hem : (signals r b St.KEY).emit = emitB sb b := by
    rw [sig_emit_inStr hstr, hsubr]
  have hcp : (signals r b St.KEY).cp = cpB sb h b := by
    rw [sig_cp_inStr hstr, hsubr]; rfl
  constructor
  · rw [step_eq e1 e2 (by rw [hw]; simp) (by rw [hw]; simp)]
    congr 1
    simp only [mkNext, kRegs, Regs.mk.injEq, hks, hkc, hve, hem, hcp, hstK, hsubr,
      Bool.false_eq_true, if_false, if_true, hexAcc_next]
    and_intros <;>
      first
        | trivial
        | (exact Vector.ext fun t ht => by simp)
        | simp [Step.inValP, St.KEY]
  · refine silent_sig0 (fun k => ?_) hve ?_ ?_
    · have hkc' : Step.keyCloseB r b = false := by rw [← Step.sig_keyClose r b St.KEY]; exact hkc
      rw [Step.sig_match, hkc']; simp
    · rw [Step.sig_minusFlag, hstK]; simp [St.KEY, St.PVAL]
    · rw [Step.sig_trueDone, hstK]; simp [St.KEY, St.T3]

theorem step_sRegs {sb sb' : Sub} {h : ℕ} {c : Option Claim} {o n : ℕ} {b : ℕ}
    (hsub : stepSub true sb b = some sb')
    (hq : ((b == quote) && decide (sb = Sub.PLAIN)) = false)
    (hcap : emitB sb b = true → (kindOf c = Kind.str ∨ kindOf c = Kind.int) →
      ∀ k : Claim, c = some k → o < claimCap k)
    (hascii : emitB sb b = true → (kindOf c = Kind.str ∨ kindOf c = Kind.int) →
      cpB sb h b < 0x80) :
    step (sRegs sb h c o n) b = some (sRegs sb'
      (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * h + Model.hexVal b else 0) c
      (min (o + (if emitB sb b then 1 else 0)) (ofsMax - 1)) n) ∧
    (∀ k : Claim, pMatch k (sRegs sb h c o n, b) = false) ∧
    (∀ k : Claim, pEmit k (sRegs sb h c o n, b) = (emitB sb b && decide (c = some k))) ∧
    fVal (sRegs sb h c o n, b) = (if emitB sb b then cpB sb h b else 0) ∧
    (∀ k : Claim, pMinus k (sRegs sb h c o n, b) = false) ∧
    (∀ k : Claim, pTrue k (sRegs sb h c o n, b) = false) := by
  set r : Regs := sRegs sb h c o n with hr
  have hstS : r.st = St.STR := rfl
  have hsubr : r.sub = sb := rfl
  have hclr : r.claim = c := rfl
  have hstr : inStr r.st = true := by rw [hstS]; rfl
  have e1 : stepSub (inStr r.st) r.sub b = some sb' := by rw [hstr, hsubr]; exact hsub
  have e2 : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b = some St.STR := by
    rw [hstS, hsubr]; exact stepSt_str_stay _ _ hq
  have hem : (signals r b St.STR).emit = emitB sb b := by
    rw [sig_emit_inStr hstr, hsubr]
  have hcp : (signals r b St.STR).cp = cpB sb h b := by
    rw [sig_cp_inStr hstr, hsubr]; rfl
  have hve : (signals r b St.STR).vEmit = emitB sb b := by
    rw [Step.sig_vEmit, Step.strEmitB, Step.digitEmitB, hstS, hem]
    simp [St.STR, St.PVAL, St.NSIGN, St.NINT]
  have hwr : (signals r b St.STR).write
      = (emitB sb b && (decide (kindOf c = Kind.str) || decide (kindOf c = Kind.int))) := by
    rw [Step.sig_write, ← Step.sig_vEmit r b St.STR, hve, hclr]
  have hks : (signals r b St.STR).keyStart = false := by rw [sig_keyStart]; simp [St.STR, St.KEY]
  have hkc : (signals r b St.STR).keyClose = false := by
    rw [Step.sig_keyClose, Step.keyCloseB, hstS]; simp [St.STR, St.KEY]
  have hcap' : (signals r b St.STR).write = true → ∀ k : Claim, r.claim = some k →
      r.ofs < claimCap k := by
    intro hw k hk
    rw [hwr, Bool.and_eq_true] at hw
    exact hcap hw.1 (by simpa using hw.2) k (by rw [← hclr]; exact hk)
  have hascii' : (signals r b St.STR).write = true → r.st = St.STR →
      (signals r b St.STR).cp < 0x80 := by
    intro hw _
    rw [hwr, Bool.and_eq_true] at hw
    rw [hcp]
    exact hascii hw.1 (by simpa using hw.2)
  refine ⟨?_, fun k => ?_, fun k => ?_, ?_, fun k => ?_, fun k => ?_⟩
  · rw [step_eq e1 e2 hcap' hascii']
    congr 1
    simp only [mkNext, sRegs, Regs.mk.injEq, hks, hkc, hve, hstS, hsubr, hclr,
      Bool.false_eq_true, if_false, hexAcc_next]
    and_intros <;>
      first
        | trivial
        | (exact Vector.ext fun t ht => by simp [St.STR, St.KEY])
        | simp [Step.inValP, St.STR, St.PRE, St.OBJ, St.KEY, St.AKEY, St.PVAL, St.AVAL, St.SEP,
            St.END]
  · rw [pMatch, Step.sig_match, Step.keyCloseB, hstS]; simp [St.STR, St.KEY]
  · show ((signals r b r.st).vEmit && decide (r.claim = some k)) = (emitB sb b && decide (c = some k))
    rw [hstS, hve]
    simp only [hclr]
  · show (signals r b r.st).valOut = (if emitB sb b then cpB sb h b else 0)
    rw [hstS, Step.sig_valOut, Step.strEmitB, Step.digitEmitB, hstS, hem, hcp]
    by_cases he : emitB sb b = true <;> simp [he, St.STR, St.PVAL, St.NSIGN, St.NINT]
  · rw [pMinus, Step.sig_minusFlag]; simp [hstS, St.STR, St.PVAL]
  · rw [pTrue, Step.sig_trueDone]; simp [hstS, St.STR, St.T3]

/-! ## Normalised in-string steps -/

theorem ofFn_getElem_self (v : Vector Bool nClaims) : (Vector.ofFn fun k : Claim => v[k]) = v :=
  Vector.ext fun i hi => by simp

theorem kstep_noemit {sb sb' : Sub} {h h' i n : ℕ} {mv : Vector Bool nClaims} {b : ℕ}
    (hsub : stepSub true sb b = some sb')
    (hq : ((b == quote) && decide (sb = Sub.PLAIN)) = false)
    (hne : emitB sb b = false) (hi : i ≤ kIdxMax - 1)
    (hh : (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * h + Model.hexVal b else 0) = h') :
    step (kRegs sb h i mv n) b = some (kRegs sb' h' i mv n) ∧ Silent (kRegs sb h i mv n, b) := by
  obtain ⟨hstep, hsil⟩ := step_kRegs (sb' := sb') (h := h) (i := i) (mv := mv) (n := n) hsub hq
  refine ⟨?_, hsil⟩
  rw [hstep, hh, hne]
  simp only [Bool.false_eq_true, if_false, add_zero, Bool.not_false, Bool.true_or,
    Bool.and_true, ofFn_getElem_self, min_eq_left hi]

theorem kstep_emit {sb sb' : Sub} {h h' i n : ℕ} {mv : Vector Bool nClaims} {b cp : ℕ}
    (hsub : stepSub true sb b = some sb')
    (hq : ((b == quote) && decide (sb = Sub.PLAIN)) = false)
    (he : emitB sb b = true) (hcp : cpB sb h b = cp)
    (hh : (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * h + Model.hexVal b else 0) = h') :
    step (kRegs sb h i mv n) b
        = some (kRegs sb' h' (min (i + 1) (kIdxMax - 1))
            (Vector.ofFn fun k : Claim => mv[k] && decide (cp = nameAt k i)) n) ∧
      Silent (kRegs sb h i mv n, b) := by
  obtain ⟨hstep, hsil⟩ := step_kRegs (sb' := sb') (h := h) (i := i) (mv := mv) (n := n) hsub hq
  refine ⟨?_, hsil⟩
  rw [hstep, hh, he, hcp]
  simp

theorem sstep_noemit {sb sb' : Sub} {h h' : ℕ} {c : Option Claim} {o n : ℕ} {b : ℕ}
    (hsub : stepSub true sb b = some sb')
    (hq : ((b == quote) && decide (sb = Sub.PLAIN)) = false)
    (hne : emitB sb b = false) (ho : o ≤ ofsMax - 1)
    (hh : (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * h + Model.hexVal b else 0) = h') :
    step (sRegs sb h c o n) b = some (sRegs sb' h' c o n) ∧ Silent (sRegs sb h c o n, b) := by
  obtain ⟨hstep, hm, he, _, hmi, ht⟩ :=
    step_sRegs (sb' := sb') (h := h) (c := c) (o := o) (n := n) hsub hq
      (by rw [hne]; simp) (by rw [hne]; simp)
  refine ⟨?_, hm, fun k => by rw [he k, hne]; simp, hmi, ht⟩
  rw [hstep, hh, hne]
  simp only [Bool.false_eq_true, if_false, add_zero, min_eq_left ho]

theorem sstep_emit {sb sb' : Sub} {h h' : ℕ} {c : Option Claim} {o n : ℕ} {b cp : ℕ}
    (hsub : stepSub true sb b = some sb')
    (hq : ((b == quote) && decide (sb = Sub.PLAIN)) = false)
    (he : emitB sb b = true) (hcp : cpB sb h b = cp)
    (hcap : (kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ k : Claim, c = some k →
      o < claimCap k)
    (hascii : (kindOf c = Kind.str ∨ kindOf c = Kind.int) → cp < 0x80)
    (hh : (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * h + Model.hexVal b else 0) = h') :
    step (sRegs sb h c o n) b = some (sRegs sb' h' c (min (o + 1) (ofsMax - 1)) n) ∧
      (∀ k : Claim, pMatch k (sRegs sb h c o n, b) = false) ∧
      (∀ k : Claim, pEmit k (sRegs sb h c o n, b) = decide (c = some k)) ∧
      fVal (sRegs sb h c o n, b) = cp ∧
      (∀ k : Claim, pMinus k (sRegs sb h c o n, b) = false) ∧
      (∀ k : Claim, pTrue k (sRegs sb h c o n, b) = false) := by
  obtain ⟨hstep, hm, hem, hv, hmi, ht⟩ :=
    step_sRegs (sb' := sb') (h := h) (c := c) (o := o) (n := n) hsub hq
      (fun _ hk => hcap hk) (fun _ hk => by rw [hcp]; exact hascii hk)
  refine ⟨?_, hm, fun k => ?_, ?_, hmi, ht⟩
  · rw [hstep, hh, he]; simp
  · rw [hem k, he]; simp
  · rw [hv, he, hcp]; simp

/-! ## Bundled contributions -/

/-- The trace `T` closes `mt` keys of `c`, routes the values `vs` to `c`, and
reads `sg` signs and `tr` trues for `c`; no other claim gets anything. -/
def Contrib (c : Option Claim) (mt : ℕ) (vs : List ℕ) (sg tr : ℕ)
    (T : List (Regs × ℕ)) : Prop :=
  (∀ k : Claim, cMatch k T = if c = some k then mt else 0) ∧
  (∀ k : Claim, valsT k T = if c = some k then vs else []) ∧
  (∀ k : Claim, cSign k T = if c = some k then sg else 0) ∧
  (∀ k : Claim, cTrue k T = if c = some k then tr else 0)

theorem contrib_of_quiet {T : List (Regs × ℕ)} (h : Quiet T) (c : Option Claim) :
    Contrib c 0 [] 0 0 T :=
  ⟨fun k => by rw [cMatch_of_quiet h]; split <;> rfl,
   fun k => by rw [valsT_of_quiet h]; split <;> rfl,
   fun k => by rw [cSign_of_quiet h]; split <;> rfl,
   fun k => by rw [cTrue_of_quiet h]; split <;> rfl⟩

theorem contrib_append {c : Option Claim} {m1 m2 : ℕ} {v1 v2 : List ℕ} {s1 s2 t1 t2 : ℕ}
    {T1 T2 : List (Regs × ℕ)} (h1 : Contrib c m1 v1 s1 t1 T1) (h2 : Contrib c m2 v2 s2 t2 T2) :
    Contrib c (m1 + m2) (v1 ++ v2) (s1 + s2) (t1 + t2) (T1 ++ T2) := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [cMatch_append, h1.1 k, h2.1 k]; split <;> simp
  · rw [valsT_append, h1.2.1 k, h2.2.1 k]; split <;> simp
  · rw [cSign_append, h1.2.2.1 k, h2.2.2.1 k]; split <;> simp
  · rw [cTrue_append, h1.2.2.2 k, h2.2.2.2 k]; split <;> simp

/-- Run a list of bytes that contributes nothing, in front of a run. -/
theorem runQ_cons {r r' rf : Regs} {b : ℕ} {L : List ℕ}
    (h1 : step r b = some r') (q1 : Silent (r, b))
    (h2 : runL r' L = some rf) (q2 : Quiet (traceL r' L)) :
    runL r (b :: L) = some rf ∧ Quiet (traceL r (b :: L)) := by
  refine ⟨by rw [RunList.runL_cons, h1, Option.bind_some]; exact h2, ?_⟩
  rw [RunList.traceL_cons_of_some h1]
  exact quiet_cons q1 q2

theorem runQ_nil (r : Regs) : runL r [] = some r ∧ Quiet (traceL r []) := ⟨rfl, quiet_nil⟩

theorem runC_cons {r r' rf : Regs} {b : ℕ} {L : List ℕ} {c : Option Claim}
    {m : ℕ} {vs : List ℕ} {sg tr : ℕ}
    (h1 : step r b = some r') (q1 : Silent (r, b))
    (h2 : runL r' L = some rf) (q2 : Contrib c m vs sg tr (traceL r' L)) :
    runL r (b :: L) = some rf ∧ Contrib c m vs sg tr (traceL r (b :: L)) := by
  refine ⟨by rw [RunList.runL_cons, h1, Option.bind_some]; exact h2, ?_⟩
  rw [RunList.traceL_cons_of_some h1]
  have := contrib_append (contrib_of_quiet (quiet_single q1) c) q2
  simpa using this

/-! ## Emission facts of the sub-states -/

@[simp] theorem emitB_plain (b : ℕ) : emitB Sub.PLAIN b = Model.isUnescaped b := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1]
@[simp] theorem emitB_esc (b : ℕ) : emitB Sub.ESC b = Model.isSimpleEsc b := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1]
@[simp] theorem emitB_h4 (b : ℕ) : emitB Sub.H4 b = Model.isHex b := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1]
@[simp] theorem emitB_c1 (b : ℕ) : emitB Sub.C1 b = Model.isCont b := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1]
@[simp] theorem emitB_h1 (b : ℕ) : emitB Sub.H1 b = false := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.H1, Sub.H4, Sub.C1]
@[simp] theorem emitB_h2 (b : ℕ) : emitB Sub.H2 b = false := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.H2, Sub.H4, Sub.C1]
@[simp] theorem emitB_h3 (b : ℕ) : emitB Sub.H3 b = false := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.H3, Sub.H4, Sub.C1]
@[simp] theorem emitB_c2 (b : ℕ) : emitB Sub.C2 b = false := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.C2, Sub.H4, Sub.C1]
@[simp] theorem emitB_c3 (b : ℕ) : emitB Sub.C3 b = false := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.C3, Sub.H4, Sub.C1]
@[simp] theorem emitB_e0s (b : ℕ) : emitB Sub.E0s b = false := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.E0s, Sub.H4, Sub.C1]
@[simp] theorem emitB_eds (b : ℕ) : emitB Sub.EDs b = false := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.EDs, Sub.H4, Sub.C1]
@[simp] theorem emitB_f0s (b : ℕ) : emitB Sub.F0s b = false := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.F0s, Sub.H4, Sub.C1]
@[simp] theorem emitB_f4s (b : ℕ) : emitB Sub.F4s b = false := by
  simp [emitB, Sub.PLAIN, Sub.ESC, Sub.F4s, Sub.H4, Sub.C1]

theorem cpB_plain {b : ℕ} (h : Model.isUnescaped b = true) (hx : ℕ) : cpB Sub.PLAIN hx b = b := by
  simp [cpB, Sub.PLAIN, h]
theorem cpB_esc {b : ℕ} (h : Model.isSimpleEsc b = true) (hx : ℕ) :
    cpB Sub.ESC hx b = Model.escVal b := by
  simp [cpB, Sub.PLAIN, Sub.ESC, h]
theorem cpB_h4 {b : ℕ} (h : Model.isHex b = true) (hx : ℕ) :
    cpB Sub.H4 hx b = 16 * hx + Model.hexVal b := by
  simp [cpB, Sub.PLAIN, Sub.ESC, Sub.H4, h]
theorem cpB_c1 {b : ℕ} (h : Model.isCont b = true) (hx : ℕ) :
    cpB Sub.C1 hx b = Model.nonAsciiMarker := by
  simp [cpB, Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1, h]

theorem hexAcc_zero_plain (hx b : ℕ) :
    (if Sub.PLAIN = Sub.H1 ∨ Sub.PLAIN = Sub.H2 ∨ Sub.PLAIN = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_zero_esc (hx b : ℕ) :
    (if Sub.ESC = Sub.H1 ∨ Sub.ESC = Sub.H2 ∨ Sub.ESC = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_zero_h4 (hx b : ℕ) :
    (if Sub.H4 = Sub.H1 ∨ Sub.H4 = Sub.H2 ∨ Sub.H4 = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_zero_c1 (hx b : ℕ) :
    (if Sub.C1 = Sub.H1 ∨ Sub.C1 = Sub.H2 ∨ Sub.C1 = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_zero_c2 (hx b : ℕ) :
    (if Sub.C2 = Sub.H1 ∨ Sub.C2 = Sub.H2 ∨ Sub.C2 = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_zero_c3 (hx b : ℕ) :
    (if Sub.C3 = Sub.H1 ∨ Sub.C3 = Sub.H2 ∨ Sub.C3 = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_zero_e0s (hx b : ℕ) :
    (if Sub.E0s = Sub.H1 ∨ Sub.E0s = Sub.H2 ∨ Sub.E0s = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_zero_eds (hx b : ℕ) :
    (if Sub.EDs = Sub.H1 ∨ Sub.EDs = Sub.H2 ∨ Sub.EDs = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_zero_f0s (hx b : ℕ) :
    (if Sub.F0s = Sub.H1 ∨ Sub.F0s = Sub.H2 ∨ Sub.F0s = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_zero_f4s (hx b : ℕ) :
    (if Sub.F4s = Sub.H1 ∨ Sub.F4s = Sub.H2 ∨ Sub.F4s = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 0 := by rw [if_neg (by decide)]
theorem hexAcc_h1 (hx b : ℕ) :
    (if Sub.H1 = Sub.H1 ∨ Sub.H1 = Sub.H2 ∨ Sub.H1 = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 16 * hx + Model.hexVal b := by rw [if_pos (by decide)]
theorem hexAcc_h2 (hx b : ℕ) :
    (if Sub.H2 = Sub.H1 ∨ Sub.H2 = Sub.H2 ∨ Sub.H2 = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 16 * hx + Model.hexVal b := by rw [if_pos (by decide)]
theorem hexAcc_h3 (hx b : ℕ) :
    (if Sub.H3 = Sub.H1 ∨ Sub.H3 = Sub.H2 ∨ Sub.H3 = Sub.H3 then
      16 * hx + Model.hexVal b else 0) = 16 * hx + Model.hexVal b := by rw [if_pos (by decide)]

theorem notQuote_of_sub {sb : Sub} (h : sb ≠ Sub.PLAIN) (b : ℕ) :
    ((b == quote) && decide (sb = Sub.PLAIN)) = false := by simp [h]

theorem notQuote_of_high {b : ℕ} (h : 0x80 ≤ b) :
    ((b == quote) && decide (Sub.PLAIN = Sub.PLAIN)) = false := by
  have : (b == quote) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x22; omega
  simp [this]

/-! ## The run of one string-body element -/

theorem isUnescaped_false_of_high {b : ℕ} (h : 0x80 ≤ b) : Model.isUnescaped b = false := by
  simp only [Model.isUnescaped, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
  left; left; right; show 0x7F < b; omega

theorem high_of_lead2 {b : ℕ} (h : Model.isLead2 b = true) : 0x80 ≤ b := by
  simp only [Model.isLead2, Bool.and_eq_true, decide_eq_true_eq] at h; omega
theorem high_of_lead3 {b : ℕ} (h : Model.isLead3 b = true) : 0x80 ≤ b := by
  simp only [Model.isLead3, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h; omega
theorem high_of_lead4 {b : ℕ} (h : Model.isLead4 b = true) : 0x80 ≤ b := by
  simp only [Model.isLead4, Bool.and_eq_true, decide_eq_true_eq] at h; omega

theorem contrib_emit {r : Regs} {b : ℕ} {c : Option Claim} {cp : ℕ}
    (hm : ∀ k : Claim, pMatch k (r, b) = false)
    (hem : ∀ k : Claim, pEmit k (r, b) = decide (c = some k))
    (hv : fVal (r, b) = cp)
    (hmi : ∀ k : Claim, pMinus k (r, b) = false)
    (ht : ∀ k : Claim, pTrue k (r, b) = false) : Contrib c 0 [cp] 0 0 [(r, b)] := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [cMatch_cons, hm k]; simp
  · rw [valsT_cons, hem k, hv]; by_cases hk : c = some k <;> simp [hk]
  · rw [cSign_cons, hmi k]; simp
  · rw [cTrue_cons, ht k]; simp

theorem runV_single {r r' : Regs} {b : ℕ} {c : Option Claim} {cp : ℕ}
    (h1 : step r b = some r')
    (hm : ∀ k : Claim, pMatch k (r, b) = false)
    (hem : ∀ k : Claim, pEmit k (r, b) = decide (c = some k))
    (hv : fVal (r, b) = cp)
    (hmi : ∀ k : Claim, pMinus k (r, b) = false)
    (ht : ∀ k : Claim, pTrue k (r, b) = false) :
    runL r [b] = some r' ∧ Contrib c 0 [cp] 0 0 (traceL r [b]) := by
  refine ⟨by rw [RunList.runL_single]; exact h1, ?_⟩
  rw [RunList.traceL_single]
  exact contrib_emit hm hem hv hmi ht

set_option maxHeartbeats 1000000 in
theorem se_run_key {e : Serial.SE} (hwf : e.WF) {h i n : ℕ} (hi : i ≤ kIdxMax - 1)
    {mv : Vector Bool nClaims} :
    runL (kRegs Sub.PLAIN h i mv n) e.bytes
      = some (kRegs Sub.PLAIN 0 (min (i + 1) (kIdxMax - 1))
          (Vector.ofFn fun k : Claim => mv[k] && decide (e.mcp = nameAt k i)) n) ∧
      Quiet (traceL (kRegs Sub.PLAIN h i mv n) e.bytes) := by
  have bslash_q : ((backslash == quote) && decide (Sub.PLAIN = Sub.PLAIN)) = false := by decide
  cases e with
  | plain b =>
    have hu : Model.isUnescaped b = true := hwf
    obtain ⟨s1, q1⟩ := kstep_emit (i := i) (mv := mv) (n := n) (h := h) (cp := b)
      (stepSub_plain_unesc hu) (by simp [RunTheory.isUnescaped_ne_quote hu])
      (by simp [hu]) (cpB_plain hu h) (hexAcc_zero_plain h b)
    exact runQ_cons s1 q1 (runQ_nil _).1 (runQ_nil _).2
  | esc b =>
    have hs : Model.isSimpleEsc b = true := hwf
    obtain ⟨s1, q1⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := h)
      stepSub_plain_bslash bslash_q (by decide) hi (hexAcc_zero_plain h backslash)
    obtain ⟨s2, q2⟩ := kstep_emit (i := i) (mv := mv) (n := n) (h := 0)
      (cp := Model.escVal b) (stepSub_esc_simple hs) (notQuote_of_sub (by decide) b)
      (by simp [hs]) (cpB_esc hs 0) (hexAcc_zero_esc 0 b)
    obtain ⟨t2, u2⟩ := runQ_cons s2 q2 (runQ_nil _).1 (runQ_nil _).2
    exact runQ_cons s1 q1 t2 u2
  | hex a b c d =>
    obtain ⟨ha, hb, hc, hd⟩ := hwf
    obtain ⟨s1, q1⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := h)
      stepSub_plain_bslash bslash_q (by decide) hi (hexAcc_zero_plain h backslash)
    obtain ⟨s2, q2⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := 0)
      stepSub_esc_u (notQuote_of_sub (by decide) lowerU) (by decide) hi (hexAcc_zero_esc 0 lowerU)
    obtain ⟨s3, q3⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := 0)
      (stepSub_h1 ha) (notQuote_of_sub (by decide) a) (by simp) hi (hexAcc_h1 0 a)
    obtain ⟨s4, q4⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := 16 * 0 + Model.hexVal a)
      (stepSub_h2 hb) (notQuote_of_sub (by decide) b) (by simp) hi (hexAcc_h2 _ b)
    obtain ⟨s5, q5⟩ := kstep_noemit (i := i) (mv := mv) (n := n)
      (h := 16 * (16 * 0 + Model.hexVal a) + Model.hexVal b)
      (stepSub_h3 hc) (notQuote_of_sub (by decide) c) (by simp) hi (hexAcc_h3 _ c)
    obtain ⟨s6, q6⟩ := kstep_emit (i := i) (mv := mv) (n := n)
      (h := 16 * (16 * (16 * 0 + Model.hexVal a) + Model.hexVal b) + Model.hexVal c)
      (cp := Serial.hexNum a b c d)
      (stepSub_h4 hd) (notQuote_of_sub (by decide) d) (by simp [hd])
      (by rw [cpB_h4 hd]; simp [Serial.hexNum]; ring) (hexAcc_zero_h4 _ d)
    obtain ⟨t6, u6⟩ := runQ_cons s6 q6 (runQ_nil _).1 (runQ_nil _).2
    obtain ⟨t5, u5⟩ := runQ_cons s5 q5 t6 u6
    obtain ⟨t4, u4⟩ := runQ_cons s4 q4 t5 u5
    obtain ⟨t3, u3⟩ := runQ_cons s3 q3 t4 u4
    obtain ⟨t2, u2⟩ := runQ_cons s2 q2 t3 u3
    exact runQ_cons s1 q1 t2 u2
  | u2 b0 b1 =>
    obtain ⟨h0, h1c⟩ := hwf
    obtain ⟨s1, q1⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := h)
      (stepSub_plain_lead2 h0) (notQuote_of_high (high_of_lead2 h0))
      (by simp [isUnescaped_false_of_high (high_of_lead2 h0)]) hi (hexAcc_zero_plain h b0)
    obtain ⟨s2, q2⟩ := kstep_emit (i := i) (mv := mv) (n := n) (h := 0)
      (cp := Model.nonAsciiMarker) (stepSub_c1 h1c) (notQuote_of_sub (by decide) b1)
      (by simp [h1c]) (cpB_c1 h1c 0) (hexAcc_zero_c1 0 b1)
    obtain ⟨t2, u2⟩ := runQ_cons s2 q2 (runQ_nil _).1 (runQ_nil _).2
    exact runQ_cons s1 q1 t2 u2
  | u3 b0 b1 b2 =>
    obtain ⟨hlead, h2c⟩ := hwf
    have hstep12 : ∃ sb, stepSub true Sub.PLAIN b0 = some sb ∧ 0x80 ≤ b0 ∧
        stepSub true sb b1 = some Sub.C1 ∧ sb ≠ Sub.PLAIN ∧ emitB sb b1 = false ∧
        (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * 0 + Model.hexVal b1 else 0) = 0 := by
      rcases hlead with ⟨rfl, hb1⟩ | ⟨hb0, hb1⟩ | ⟨rfl, hb1⟩
      · exact ⟨Sub.E0s, stepSub_plain_e0, by norm_num, stepSub_e0s hb1, by decide, by simp,
          hexAcc_zero_e0s 0 b1⟩
      · exact ⟨Sub.C2, stepSub_plain_lead3 hb0, high_of_lead3 hb0, stepSub_c2 hb1, by decide,
          by simp, hexAcc_zero_c2 0 b1⟩
      · exact ⟨Sub.EDs, stepSub_plain_ed, by norm_num, stepSub_eds hb1, by decide, by simp,
          hexAcc_zero_eds 0 b1⟩
    obtain ⟨sb, hsb0, hhigh, hsb1, hsbne, hsbe, hsbh⟩ := hstep12
    obtain ⟨s1, q1⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := h)
      hsb0 (notQuote_of_high hhigh) (by simp [isUnescaped_false_of_high hhigh]) hi
      (hexAcc_zero_plain h b0)
    obtain ⟨s2, q2⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := 0)
      hsb1 (notQuote_of_sub hsbne b1) hsbe hi hsbh
    obtain ⟨s3, q3⟩ := kstep_emit (i := i) (mv := mv) (n := n) (h := 0)
      (cp := Model.nonAsciiMarker) (stepSub_c1 h2c) (notQuote_of_sub (by decide) b2)
      (by simp [h2c]) (cpB_c1 h2c 0) (hexAcc_zero_c1 0 b2)
    obtain ⟨t3, u3⟩ := runQ_cons s3 q3 (runQ_nil _).1 (runQ_nil _).2
    obtain ⟨t2, u2⟩ := runQ_cons s2 q2 t3 u3
    exact runQ_cons s1 q1 t2 u2
  | u4 b0 b1 b2 b3 =>
    obtain ⟨hlead, h2c, h3c⟩ := hwf
    have hstep12 : ∃ sb, stepSub true Sub.PLAIN b0 = some sb ∧ 0x80 ≤ b0 ∧
        stepSub true sb b1 = some Sub.C2 ∧ sb ≠ Sub.PLAIN ∧ emitB sb b1 = false ∧
        (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * 0 + Model.hexVal b1 else 0) = 0 := by
      rcases hlead with ⟨rfl, hb1⟩ | ⟨hb0, hb1⟩ | ⟨rfl, hb1⟩
      · exact ⟨Sub.F0s, stepSub_plain_f0, by norm_num, stepSub_f0s hb1, by decide, by simp,
          hexAcc_zero_f0s 0 b1⟩
      · exact ⟨Sub.C3, stepSub_plain_lead4 hb0, high_of_lead4 hb0, stepSub_c3 hb1, by decide,
          by simp, hexAcc_zero_c3 0 b1⟩
      · exact ⟨Sub.F4s, stepSub_plain_f4, by norm_num, stepSub_f4s hb1, by decide, by simp,
          hexAcc_zero_f4s 0 b1⟩
    obtain ⟨sb, hsb0, hhigh, hsb1, hsbne, hsbe, hsbh⟩ := hstep12
    obtain ⟨s1, q1⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := h)
      hsb0 (notQuote_of_high hhigh) (by simp [isUnescaped_false_of_high hhigh]) hi
      (hexAcc_zero_plain h b0)
    obtain ⟨s2, q2⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := 0)
      hsb1 (notQuote_of_sub hsbne b1) hsbe hi hsbh
    obtain ⟨s3, q3⟩ := kstep_noemit (i := i) (mv := mv) (n := n) (h := 0)
      (stepSub_c2 h2c) (notQuote_of_sub (by decide) b2) (by simp) hi (hexAcc_zero_c2 0 b2)
    obtain ⟨s4, q4⟩ := kstep_emit (i := i) (mv := mv) (n := n) (h := 0)
      (cp := Model.nonAsciiMarker) (stepSub_c1 h3c) (notQuote_of_sub (by decide) b3)
      (by simp [h3c]) (cpB_c1 h3c 0) (hexAcc_zero_c1 0 b3)
    obtain ⟨t4, u4⟩ := runQ_cons s4 q4 (runQ_nil _).1 (runQ_nil _).2
    obtain ⟨t3, u3⟩ := runQ_cons s3 q3 t4 u4
    obtain ⟨t2, u2⟩ := runQ_cons s2 q2 t3 u3
    exact runQ_cons s1 q1 t2 u2

set_option maxHeartbeats 1000000 in
theorem se_run_str {e : Serial.SE} (hwf : e.WF) {h : ℕ} {c : Option Claim} {o n : ℕ}
    (ho : o ≤ ofsMax - 1)
    (hcap : (kindOf c = Kind.str ∨ kindOf c = Kind.int) → ∀ k : Claim, c = some k →
      o < claimCap k)
    (hascii : (kindOf c = Kind.str ∨ kindOf c = Kind.int) → e.mcp < 0x80) :
    runL (sRegs Sub.PLAIN h c o n) e.bytes
        = some (sRegs Sub.PLAIN 0 c (min (o + 1) (ofsMax - 1)) n) ∧
      Contrib c 0 [e.mcp] 0 0 (traceL (sRegs Sub.PLAIN h c o n) e.bytes) := by
  have bslash_q : ((backslash == quote) && decide (Sub.PLAIN = Sub.PLAIN)) = false := by decide
  cases e with
  | plain b =>
    have hu : Model.isUnescaped b = true := hwf
    obtain ⟨s1, m1, e1, v1, mi1, t1⟩ := sstep_emit (c := c) (o := o) (n := n) (h := h) (cp := b)
      (stepSub_plain_unesc hu) (by simp [RunTheory.isUnescaped_ne_quote hu])
      (by simp [hu]) (cpB_plain hu h) hcap hascii (hexAcc_zero_plain h b)
    exact runV_single s1 m1 e1 v1 mi1 t1
  | esc b =>
    have hs : Model.isSimpleEsc b = true := hwf
    obtain ⟨s1, q1⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := h)
      stepSub_plain_bslash bslash_q (by decide) ho (hexAcc_zero_plain h backslash)
    obtain ⟨s2, m2, e2, v2, mi2, t2⟩ := sstep_emit (c := c) (o := o) (n := n) (h := 0)
      (cp := Model.escVal b) (stepSub_esc_simple hs) (notQuote_of_sub (by decide) b)
      (by simp [hs]) (cpB_esc hs 0) hcap hascii (hexAcc_zero_esc 0 b)
    obtain ⟨r2, c2⟩ := runV_single s2 m2 e2 v2 mi2 t2
    exact runC_cons s1 q1 r2 c2
  | hex a b c' d =>
    obtain ⟨ha, hb, hc, hd⟩ := hwf
    obtain ⟨s1, q1⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := h)
      stepSub_plain_bslash bslash_q (by decide) ho (hexAcc_zero_plain h backslash)
    obtain ⟨s2, q2⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      stepSub_esc_u (notQuote_of_sub (by decide) lowerU) (by decide) ho (hexAcc_zero_esc 0 lowerU)
    obtain ⟨s3, q3⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      (stepSub_h1 ha) (notQuote_of_sub (by decide) a) (by simp) ho (hexAcc_h1 0 a)
    obtain ⟨s4, q4⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 16 * 0 + Model.hexVal a)
      (stepSub_h2 hb) (notQuote_of_sub (by decide) b) (by simp) ho (hexAcc_h2 _ b)
    obtain ⟨s5, q5⟩ := sstep_noemit (c := c) (o := o) (n := n)
      (h := 16 * (16 * 0 + Model.hexVal a) + Model.hexVal b)
      (stepSub_h3 hc) (notQuote_of_sub (by decide) c') (by simp) ho (hexAcc_h3 _ c')
    obtain ⟨s6, m6, e6, v6, mi6, t6⟩ := sstep_emit (c := c) (o := o) (n := n)
      (h := 16 * (16 * (16 * 0 + Model.hexVal a) + Model.hexVal b) + Model.hexVal c')
      (cp := Serial.hexNum a b c' d)
      (stepSub_h4 hd) (notQuote_of_sub (by decide) d) (by simp [hd])
      (by rw [cpB_h4 hd]; simp [Serial.hexNum]; ring) hcap hascii (hexAcc_zero_h4 _ d)
    obtain ⟨r6, k6⟩ := runV_single s6 m6 e6 v6 mi6 t6
    obtain ⟨r5, k5⟩ := runC_cons s5 q5 r6 k6
    obtain ⟨r4, k4⟩ := runC_cons s4 q4 r5 k5
    obtain ⟨r3, k3⟩ := runC_cons s3 q3 r4 k4
    obtain ⟨r2, k2⟩ := runC_cons s2 q2 r3 k3
    exact runC_cons s1 q1 r2 k2
  | u2 b0 b1 =>
    obtain ⟨h0, h1c⟩ := hwf
    obtain ⟨s1, q1⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := h)
      (stepSub_plain_lead2 h0) (notQuote_of_high (high_of_lead2 h0))
      (by simp [isUnescaped_false_of_high (high_of_lead2 h0)]) ho (hexAcc_zero_plain h b0)
    obtain ⟨s2, m2, e2, v2, mi2, t2⟩ := sstep_emit (c := c) (o := o) (n := n) (h := 0)
      (cp := Model.nonAsciiMarker) (stepSub_c1 h1c) (notQuote_of_sub (by decide) b1)
      (by simp [h1c]) (cpB_c1 h1c 0) hcap hascii (hexAcc_zero_c1 0 b1)
    obtain ⟨r2, k2⟩ := runV_single s2 m2 e2 v2 mi2 t2
    exact runC_cons s1 q1 r2 k2
  | u3 b0 b1 b2 =>
    obtain ⟨hlead, h2c⟩ := hwf
    have hstep12 : ∃ sb, stepSub true Sub.PLAIN b0 = some sb ∧ 0x80 ≤ b0 ∧
        stepSub true sb b1 = some Sub.C1 ∧ sb ≠ Sub.PLAIN ∧ emitB sb b1 = false ∧
        (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * 0 + Model.hexVal b1 else 0) = 0 := by
      rcases hlead with ⟨rfl, hb1⟩ | ⟨hb0, hb1⟩ | ⟨rfl, hb1⟩
      · exact ⟨Sub.E0s, stepSub_plain_e0, by norm_num, stepSub_e0s hb1, by decide, by simp,
          hexAcc_zero_e0s 0 b1⟩
      · exact ⟨Sub.C2, stepSub_plain_lead3 hb0, high_of_lead3 hb0, stepSub_c2 hb1, by decide,
          by simp, hexAcc_zero_c2 0 b1⟩
      · exact ⟨Sub.EDs, stepSub_plain_ed, by norm_num, stepSub_eds hb1, by decide, by simp,
          hexAcc_zero_eds 0 b1⟩
    obtain ⟨sb, hsb0, hhigh, hsb1, hsbne, hsbe, hsbh⟩ := hstep12
    obtain ⟨s1, q1⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := h)
      hsb0 (notQuote_of_high hhigh) (by simp [isUnescaped_false_of_high hhigh]) ho
      (hexAcc_zero_plain h b0)
    obtain ⟨s2, q2⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      hsb1 (notQuote_of_sub hsbne b1) hsbe ho hsbh
    obtain ⟨s3, m3, e3, v3, mi3, t3⟩ := sstep_emit (c := c) (o := o) (n := n) (h := 0)
      (cp := Model.nonAsciiMarker) (stepSub_c1 h2c) (notQuote_of_sub (by decide) b2)
      (by simp [h2c]) (cpB_c1 h2c 0) hcap hascii (hexAcc_zero_c1 0 b2)
    obtain ⟨r3, k3⟩ := runV_single s3 m3 e3 v3 mi3 t3
    obtain ⟨r2, k2⟩ := runC_cons s2 q2 r3 k3
    exact runC_cons s1 q1 r2 k2
  | u4 b0 b1 b2 b3 =>
    obtain ⟨hlead, h2c, h3c⟩ := hwf
    have hstep12 : ∃ sb, stepSub true Sub.PLAIN b0 = some sb ∧ 0x80 ≤ b0 ∧
        stepSub true sb b1 = some Sub.C2 ∧ sb ≠ Sub.PLAIN ∧ emitB sb b1 = false ∧
        (if sb = Sub.H1 ∨ sb = Sub.H2 ∨ sb = Sub.H3 then 16 * 0 + Model.hexVal b1 else 0) = 0 := by
      rcases hlead with ⟨rfl, hb1⟩ | ⟨hb0, hb1⟩ | ⟨rfl, hb1⟩
      · exact ⟨Sub.F0s, stepSub_plain_f0, by norm_num, stepSub_f0s hb1, by decide, by simp,
          hexAcc_zero_f0s 0 b1⟩
      · exact ⟨Sub.C3, stepSub_plain_lead4 hb0, high_of_lead4 hb0, stepSub_c3 hb1, by decide,
          by simp, hexAcc_zero_c3 0 b1⟩
      · exact ⟨Sub.F4s, stepSub_plain_f4, by norm_num, stepSub_f4s hb1, by decide, by simp,
          hexAcc_zero_f4s 0 b1⟩
    obtain ⟨sb, hsb0, hhigh, hsb1, hsbne, hsbe, hsbh⟩ := hstep12
    obtain ⟨s1, q1⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := h)
      hsb0 (notQuote_of_high hhigh) (by simp [isUnescaped_false_of_high hhigh]) ho
      (hexAcc_zero_plain h b0)
    obtain ⟨s2, q2⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      hsb1 (notQuote_of_sub hsbne b1) hsbe ho hsbh
    obtain ⟨s3, q3⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      (stepSub_c2 h2c) (notQuote_of_sub (by decide) b2) (by simp) ho (hexAcc_zero_c2 0 b2)
    obtain ⟨s4, m4, e4, v4, mi4, t4⟩ := sstep_emit (c := c) (o := o) (n := n) (h := 0)
      (cp := Model.nonAsciiMarker) (stepSub_c1 h3c) (notQuote_of_sub (by decide) b3)
      (by simp [h3c]) (cpB_c1 h3c 0) hcap hascii (hexAcc_zero_c1 0 b3)
    obtain ⟨r4, k4⟩ := runV_single s4 m4 e4 v4 mi4 t4
    obtain ⟨r3, k3⟩ := runC_cons s3 q3 r4 k4
    obtain ⟨r2, k2⟩ := runC_cons s2 q2 r3 k3
    exact runC_cons s1 q1 r2 k2

/-! ## Stepping outside strings, with an offset -/

/-- The register record outside a string, with an explicit offset. -/
def nRegs (s : St) (c : Option Claim) (o n : ℕ) : Regs :=
  { st := s, sub := Sub.PLAIN, hexAcc := 0, kIdx := 0, m := Vector.ofFn fun _ => false,
    claim := c, ofs := o, nMem := n }

theorem normal_eq (s : St) (c : Option Claim) (n : ℕ) : normal s c n = nRegs s c 0 n := rfl

/-- The digit-emission flag outside a string. -/
def dEmit (s : St) (b : ℕ) : Bool :=
  Model.isDigit b && (decide (s = St.PVAL) || decide (s = St.NSIGN) || decide (s = St.NINT))

theorem step_nRegs {s s' : St} {c : Option Claim} {o n b : ℕ}
    (hnstr : inStr s = false) (hs'k : s' ≠ St.KEY)
    (hst : stepSt (kindOf c) true s b = some s')
    (hcap : dEmit s b = true → (kindOf c = Kind.str ∨ kindOf c = Kind.int) →
      ∀ k : Claim, c = some k → o < claimCap k) :
    step (nRegs s c o n) b = some (nRegs s' c
        (min ((if Step.inValP s = true then o else 0) + (if dEmit s b then 1 else 0))
          (ofsMax - 1)) n) ∧
      (∀ k : Claim, pMatch k (nRegs s c o n, b) = false) ∧
      (∀ k : Claim, pEmit k (nRegs s c o n, b) = (dEmit s b && decide (c = some k))) ∧
      fVal (nRegs s c o n, b) = (if dEmit s b then b - digit0 else 0) ∧
      (∀ k : Claim, pMinus k (nRegs s c o n, b)
        = ((decide (s = St.PVAL) && (b == minus)) && decide (c = some k))) ∧
      (∀ k : Claim, pTrue k (nRegs s c o n, b)
        = ((decide (s = St.T3) && (b == lowerE)) && decide (c = some k))) := by
  set r : Regs := nRegs s c o n with hr
  have hstr : r.st = s := rfl
  have hsubr : r.sub = Sub.PLAIN := rfl
  have hclr : r.claim = c := rfl
  have hnk : s ≠ St.KEY := by intro h; rw [h] at hnstr; exact absurd hnstr (by decide)
  have e1 : stepSub (inStr r.st) r.sub b = some Sub.PLAIN := by
    rw [hstr, hnstr]; exact stepSub_notInStr _ _
  have e2 : stepSt (kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b = some s' := by
    rw [hstr, hsubr, hclr]; simpa using hst
  have hem : ∀ t : St, (signals r b t).emit = false :=
    fun _ => sig_emit_of_notInStr (by rw [hstr]; exact hnstr)
  have hve : ∀ t : St, (signals r b t).vEmit = dEmit s b := fun t => by
    rw [Step.sig_vEmit, Step.strEmitB, Step.digitEmitB, hem r.st, hstr, dEmit]; simp
  have hwr : (signals r b s').write
      = (dEmit s b && (decide (kindOf c = Kind.str) || decide (kindOf c = Kind.int))) := by
    rw [Step.sig_write, ← Step.sig_vEmit r b s', hve s', hclr]
  have hks : (signals r b s').keyStart = false := by rw [sig_keyStart]; simp [hs'k]
  have hkc : (signals r b s').keyClose = false := by
    rw [Step.sig_keyClose, Step.keyCloseB, hstr]; simp [hnk]
  have hcap' : (signals r b s').write = true → ∀ k : Claim, r.claim = some k →
      r.ofs < claimCap k := by
    intro hw k hk
    rw [hwr, Bool.and_eq_true] at hw
    exact hcap hw.1 (by simpa using hw.2) k (by rw [← hclr]; exact hk)
  have hascii' : (signals r b s').write = true → r.st = St.STR → (signals r b s').cp < 0x80 := by
    intro _ hs
    rw [hstr] at hs; rw [hs] at hnstr; exact absurd hnstr (by decide)
  refine ⟨?_, fun k => ?_, fun k => ?_, ?_, fun k => ?_, fun k => ?_⟩
  · rw [step_eq e1 e2 hcap' hascii']
    congr 1
    simp only [mkNext, nRegs, Regs.mk.injEq, hks, hkc, hve s', hstr, hsubr, hclr,
      Bool.false_eq_true, if_false, hexAcc_next]
    and_intros <;>
      first
        | trivial
        | (exact Vector.ext fun t ht => by simp [hnk])
        | simp [hnk, Sub.PLAIN, Sub.H1, Sub.H2, Sub.H3]
  · rw [pMatch, Step.sig_match, Step.keyCloseB, hstr]; simp [hnk]
  · show ((signals r b r.st).vEmit && decide (r.claim = some k)) = (dEmit s b && decide (c = some k))
    rw [hstr, hve s]; simp only [hclr]
  · show (signals r b r.st).valOut = _
    rw [Step.sig_valOut, Step.strEmitB, Step.digitEmitB, hem r.st, hstr]
    simp [dEmit]
  · show ((signals r b r.st).minusFlag && decide (r.claim = some k)) = _
    rw [hstr, Step.sig_minusFlag, hstr]; simp only [hclr]
  · show ((signals r b r.st).trueDone && decide (r.claim = some k)) = _
    rw [hstr, Step.sig_trueDone, hstr]; simp only [hclr]

theorem contrib_nstep {s s' : St} {c : Option Claim} {o n b : ℕ}
    (hnstr : inStr s = false) (hs'k : s' ≠ St.KEY)
    (hst : stepSt (kindOf c) true s b = some s')
    (hcap : dEmit s b = true → (kindOf c = Kind.str ∨ kindOf c = Kind.int) →
      ∀ k : Claim, c = some k → o < claimCap k) :
    step (nRegs s c o n) b = some (nRegs s' c
        (min ((if Step.inValP s = true then o else 0) + (if dEmit s b then 1 else 0))
          (ofsMax - 1)) n) ∧
      Contrib c 0 (if dEmit s b then [b - digit0] else [])
        (if (decide (s = St.PVAL) && (b == minus)) = true then 1 else 0)
        (if (decide (s = St.T3) && (b == lowerE)) = true then 1 else 0)
        (traceL (nRegs s c o n) [b]) := by
  obtain ⟨hstep, hm, hem, hv, hmi, ht⟩ := step_nRegs hnstr hs'k hst hcap
  refine ⟨hstep, ?_⟩
  rw [RunList.traceL_single]
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [cMatch_cons, hm k]; simp
  · rw [valsT_cons, hem k, hv]
    by_cases hk : c = some k <;> by_cases hd : dEmit s b = true <;> simp [hk, hd]
  · rw [cSign_cons, hmi k]
    by_cases hk : c = some k <;> simp [hk]
  · rw [cTrue_cons, ht k]
    by_cases hk : c = some k <;> simp [hk]

end SerStep

end Solution.JSONExtract
