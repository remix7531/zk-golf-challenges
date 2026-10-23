import Solution.JSONExtract.SerRun
import Solution.JSONExtract.SerParse

/-!
# An accepting run is a serialization (`JSONExtract`)

The backward half of the automaton argument: if the model accepts a byte list
then that list is `Ser.bytes` of a structurally well-formed `Ser`.  The proof
peels the run segment by segment, mirroring `SerRun.lean`.
-/

namespace Solution.JSONExtract

open Model (St Sub Claim Regs Kind nClaims kIdxMax ofsMax)

namespace RunInv

open Model
open Serial
open SerStep
open SerRun
open RunList (runL traceL)
open Specs.JSON (quote backslash slash lbrace rbrace colon comma minus plus dot
  digit0 digit9 lowerA lowerB lowerE lowerF lowerN lowerR lowerT lowerU upperA upperE upperF
  space tab lf cr backspace formfeed trueLit falseLit nullLit)

/-! ## Peeling one step -/

theorem runL_cons_inv {r rEnd : Regs} {b : ℕ} {L : List ℕ} (h : runL r (b :: L) = some rEnd) :
    ∃ r', step r b = some r' ∧ runL r' L = some rEnd := by
  rw [RunList.runL_cons] at h
  cases hs : step r b with
  | none => rw [hs] at h; simp at h
  | some r' => rw [hs] at h; simp only [Option.bind_some] at h; exact ⟨r', rfl, h⟩

/-! ## Equations of the sub-automaton -/

theorem stepSub_plain_eq (b : ℕ) : stepSub true Sub.PLAIN b =
    (if (b == quote) = true then some Sub.PLAIN
     else if Model.isUnescaped b = true then some Sub.PLAIN
     else if (b == backslash) = true then some Sub.ESC
     else if Model.isLead2 b = true then some Sub.C1
     else if (b == 0xE0) = true then some Sub.E0s
     else if Model.isLead3 b = true then some Sub.C2
     else if (b == 0xED) = true then some Sub.EDs
     else if (b == 0xF0) = true then some Sub.F0s
     else if Model.isLead4 b = true then some Sub.C3
     else if (b == 0xF4) = true then some Sub.F4s else none) := rfl

theorem stepSub_esc_eq (b : ℕ) : stepSub true Sub.ESC b =
    (if Model.isSimpleEsc b = true then some Sub.PLAIN
     else if (b == lowerU) = true then some Sub.H1 else none) := rfl

theorem stepSub_h1_eq (b : ℕ) :
    stepSub true Sub.H1 b = (if Model.isHex b = true then some Sub.H2 else none) := rfl
theorem stepSub_h2_eq (b : ℕ) :
    stepSub true Sub.H2 b = (if Model.isHex b = true then some Sub.H3 else none) := rfl
theorem stepSub_h3_eq (b : ℕ) :
    stepSub true Sub.H3 b = (if Model.isHex b = true then some Sub.H4 else none) := rfl
theorem stepSub_h4_eq (b : ℕ) :
    stepSub true Sub.H4 b = (if Model.isHex b = true then some Sub.PLAIN else none) := rfl
theorem stepSub_c1_eq (b : ℕ) :
    stepSub true Sub.C1 b = (if Model.isCont b = true then some Sub.PLAIN else none) := rfl
theorem stepSub_c2_eq (b : ℕ) :
    stepSub true Sub.C2 b = (if Model.isCont b = true then some Sub.C1 else none) := rfl
theorem stepSub_c3_eq (b : ℕ) :
    stepSub true Sub.C3 b = (if Model.isCont b = true then some Sub.C2 else none) := rfl
theorem stepSub_e0s_eq (b : ℕ) :
    stepSub true Sub.E0s b = (if Model.isContA0BF b = true then some Sub.C1 else none) := rfl
theorem stepSub_eds_eq (b : ℕ) :
    stepSub true Sub.EDs b = (if Model.isCont809F b = true then some Sub.C1 else none) := rfl
theorem stepSub_f0s_eq (b : ℕ) :
    stepSub true Sub.F0s b = (if Model.isCont90BF b = true then some Sub.C2 else none) := rfl
theorem stepSub_f4s_eq (b : ℕ) :
    stepSub true Sub.F4s b = (if Model.isCont808F b = true then some Sub.C2 else none) := rfl

/-! ## Equations of the main automaton -/

theorem stepSt_pre_eq (kind : Kind) (sp : Bool) (b : ℕ) : stepSt kind sp St.PRE b =
    (if Model.isWs b = true then some St.PRE
     else if (b == lbrace) = true then some St.OBJ else none) := rfl

theorem stepSt_obj_eq (kind : Kind) (sp : Bool) (b : ℕ) : stepSt kind sp St.OBJ b =
    (if Model.isWs b = true then some St.OBJ
     else if (b == quote) = true then some St.KEY
     else if (b == rbrace) = true then some St.END else none) := rfl

theorem stepSt_key_eq (kind : Kind) (sp : Bool) (b : ℕ) : stepSt kind sp St.KEY b =
    (if ((b == quote) && sp) = true then some St.AKEY else some St.KEY) := rfl

theorem stepSt_akey_eq (kind : Kind) (sp : Bool) (b : ℕ) : stepSt kind sp St.AKEY b =
    (if Model.isWs b = true then some St.AKEY
     else if (b == colon) = true then some St.PVAL else none) := rfl

theorem stepSt_str_eq (kind : Kind) (sp : Bool) (b : ℕ) : stepSt kind sp St.STR b =
    (if ((b == quote) && sp) = true then some St.AVAL else some St.STR) := rfl

theorem stepSt_t1_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.T1 b = (if (b == lowerR) = true then some St.T2 else none) := rfl
theorem stepSt_t2_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.T2 b = (if (b == lowerU) = true then some St.T3 else none) := rfl
theorem stepSt_t3_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.T3 b = (if (b == lowerE) = true then some St.AVAL else none) := rfl
theorem stepSt_f1_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.F1 b = (if (b == lowerA) = true then some St.F2 else none) := rfl
theorem stepSt_f2_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.F2 b = (if (b == 0x6C) = true then some St.F3 else none) := rfl
theorem stepSt_f3_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.F3 b = (if (b == 0x73) = true then some St.F4 else none) := rfl
theorem stepSt_f4_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.F4 b = (if (b == lowerE) = true then some St.AVAL else none) := rfl
theorem stepSt_n1_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.N1 b = (if (b == lowerU) = true then some St.N2 else none) := rfl
theorem stepSt_n2_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.N2 b = (if (b == 0x6C) = true then some St.N3 else none) := rfl
theorem stepSt_n3_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.N3 b = (if (b == 0x6C) = true then some St.AVAL else none) := rfl

theorem stepSt_aval_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.AVAL b = afterValue b := rfl

theorem stepSt_sep_eq (kind : Kind) (sp : Bool) (b : ℕ) : stepSt kind sp St.SEP b =
    (if Model.isWs b = true then some St.SEP
     else if (b == quote) = true then some St.KEY else none) := rfl

theorem stepSt_end_eq (kind : Kind) (sp : Bool) (b : ℕ) :
    stepSt kind sp St.END b = (if Model.isWs b = true then some St.END else none) := rfl

/-! ## Peeling whitespace -/

/-- The list does not start with whitespace. -/
def NotWsHead (L : List ℕ) : Prop := ∀ c t, L = c :: t → Model.isWs c = false

theorem notWsHead_nil : NotWsHead [] := by intro c t h; simp at h

theorem notWsHead_cons {b : ℕ} (h : Model.isWs b = false) (t : List ℕ) : NotWsHead (b :: t) := by
  intro c t' he
  rw [List.cons.injEq] at he
  rw [← he.1]; exact h

theorem ws_peel_normal {s : St} (hs : wsState s = true) {c : Option Claim} {n : ℕ} :
    ∀ (L : List ℕ) {rEnd : Regs}, runL (normal s c n) L = some rEnd →
      ∃ w L', L = w ++ L' ∧ IsWs w ∧ NotWsHead L' ∧ runL (normal s c n) L' = some rEnd := by
  intro L
  induction L with
  | nil => intro rEnd h; exact ⟨[], [], rfl, by intro x hx; simp at hx, notWsHead_nil, h⟩
  | cons b L ih =>
    intro rEnd h
    by_cases hb : Model.isWs b = true
    · have hstep : step (normal s c n) b = some (normal s c n) := by
        have := step_ws (r := normal s c n) hb (by rw [normal_st]; exact hs) (normal_sub s c n)
        rwa [normal_st, normal_claim, normal_nMem] at this
      obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
      rw [hstep] at hs1
      rw [← Option.some.inj hs1] at hrest
      obtain ⟨w, L', he, hw, hn, hr⟩ := ih hrest
      exact ⟨b :: w, L', by rw [he]; rfl,
        by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; · exact hb
           · exact hw x hx, hn, hr⟩
    · simp only [Bool.not_eq_true] at hb
      exact ⟨[], b :: L, rfl, by intro x hx; simp at hx, notWsHead_cons hb L, h⟩

theorem ws_peel {s : St} (hs : wsState s = true) {c : Option Claim} {n : ℕ} {r : Regs}
    (hr : AtS s c n r) : ∀ (L : List ℕ) {rEnd : Regs}, runL r L = some rEnd →
      ∃ w L' r', L = w ++ L' ∧ IsWs w ∧ NotWsHead L' ∧ runL r' L' = some rEnd ∧
        AtS s c n r' := by
  intro L rEnd h
  cases L with
  | nil => exact ⟨[], [], r, rfl, by intro x hx; simp at hx, notWsHead_nil, h, hr⟩
  | cons b L =>
    by_cases hb : Model.isWs b = true
    · have hstep : step r b = some (normal s c n) := by
        have := step_ws (r := r) hb (by rw [hr.1]; exact hs) hr.2.1
        rwa [hr.1, hr.2.2.1, hr.2.2.2] at this
      obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
      rw [hstep] at hs1
      rw [← Option.some.inj hs1] at hrest
      obtain ⟨w, L', he, hw, hn, hrr⟩ := ws_peel_normal hs L hrest
      exact ⟨b :: w, L', normal s c n, by rw [he]; rfl,
        by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; · exact hb
           · exact hw x hx, hn, hrr, atS_normal s c n⟩
    · simp only [Bool.not_eq_true] at hb
      exact ⟨[], b :: L, r, rfl, by intro x hx; simp at hx, notWsHead_cons hb L, h, hr⟩

theorem step_endVal_ws_aval {c : Option Claim} {n : ℕ} {r : Regs} {b : ℕ} (h : AtE c n r)
    (hb : Model.isWs b = true) : ∃ r', step r b = some r' ∧ AtE c n r' ∧ r'.st = St.AVAL := by
  obtain ⟨r', hstep, hst, hsub, hcl, hnm, -⟩ :=
    step_of_AtE h (isWs_not_digit hb) (isWs_ne_dot hb) (isWs_not_exp hb)
      (show afterValue b = some St.AVAL by rw [afterValue, if_pos hb])
  exact ⟨r', hstep, ⟨by rw [hst]; exact endValState_aval, hsub, hcl, hnm⟩, hst⟩

theorem ws_peel_AtE {c : Option Claim} {n : ℕ} :
    ∀ (L : List ℕ) {r rEnd : Regs}, AtE c n r → runL r L = some rEnd →
      ∃ w L' r', L = w ++ L' ∧ IsWs w ∧ NotWsHead L' ∧ runL r' L' = some rEnd ∧
        AtE c n r' ∧ (w = [] → r' = r) ∧ (w ≠ [] → r'.st = St.AVAL) := by
  intro L
  induction L with
  | nil =>
    intro r rEnd hr h
    exact ⟨[], [], r, rfl, by intro x hx; simp at hx, notWsHead_nil, h, hr, fun _ => rfl,
      by intro hx; exact absurd rfl hx⟩
  | cons b L ih =>
    intro r rEnd hr h
    by_cases hb : Model.isWs b = true
    · obtain ⟨r1, hstep, ha1, hav1⟩ := step_endVal_ws_aval hr hb
      obtain ⟨r2, hs2, hrest⟩ := runL_cons_inv h
      rw [hstep] at hs2
      rw [← Option.some.inj hs2] at hrest
      obtain ⟨w, L', r3, he, hw, hn, hrr, ha3, hnil3, hav3⟩ := ih ha1 hrest
      refine ⟨b :: w, L', r3, by rw [he]; rfl,
        by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; · exact hb
           · exact hw x hx, hn, hrr, ha3, by intro hx; simp at hx, ?_⟩
      intro _
      by_cases hwn : w = []
      · rw [hnil3 hwn]; exact hav1
      · exact hav3 hwn
    · simp only [Bool.not_eq_true] at hb
      exact ⟨[], b :: L, r, rfl, by intro x hx; simp at hx, notWsHead_cons hb L, h, hr,
        fun _ => rfl, by intro hx; exact absurd rfl hx⟩

/-! ## Peeling one byte inside a string -/

theorem inStr_ne_end {s : St} (h : inStr s = true) : s ≠ St.END := by
  revert h; revert s; decide

theorem st_stay {r r' : Regs} {b : ℕ} (hstr : inStr r.st = true) (h : step r b = some r')
    (hq : ((b == quote) && decide (r.sub = Sub.PLAIN)) = false) : r'.st = r.st := by
  have hst := (Step.step_fields h).2.1
  simp only [inStr, Bool.or_eq_true, decide_eq_true_eq] at hstr
  rcases hstr with hk | hk
  · rw [hk] at hst ⊢
    rw [stepSt_key_eq, if_neg (by simp [hq])] at hst
    exact (Option.some.inj hst).symm
  · rw [hk] at hst ⊢
    rw [stepSt_str_eq, if_neg (by simp [hq])] at hst
    exact (Option.some.inj hst).symm

/-- One byte inside a string, when the sub-state is not `PLAIN`. -/
theorem peel_sub {r rEnd : Regs} {L : List ℕ} (hstr : inStr r.st = true)
    (hsub : r.sub ≠ Sub.PLAIN) (h : runL r L = some rEnd) (hend : rEnd.st = St.END) :
    ∃ b L' r', L = b :: L' ∧ stepSub true r.sub b = some r'.sub ∧ r'.st = r.st ∧
      runL r' L' = some rEnd := by
  cases L with
  | nil =>
    exfalso
    rw [RunList.runL_nil, Option.some.injEq] at h
    rw [← h] at hend
    exact inStr_ne_end hstr hend
  | cons b L' =>
    obtain ⟨r', hs, hrest⟩ := runL_cons_inv h
    have hq : ((b == quote) && decide (r.sub = Sub.PLAIN)) = false := by simp [hsub]
    refine ⟨b, L', r', rfl, ?_, st_stay hstr hs hq, hrest⟩
    have := (Step.step_fields hs).1
    rwa [hstr] at this

/-- One byte inside a string at `PLAIN`, when it is not the closing quote. -/
theorem peel_plain {r rEnd : Regs} {b : ℕ} {L : List ℕ} (hstr : inStr r.st = true)
    (hsub : r.sub = Sub.PLAIN) (hq : (b == quote) = false)
    (h : runL r (b :: L) = some rEnd) :
    ∃ r', stepSub true Sub.PLAIN b = some r'.sub ∧ r'.st = r.st ∧ runL r' L = some rEnd := by
  obtain ⟨r', hs, hrest⟩ := runL_cons_inv h
  refine ⟨r', ?_, st_stay hstr hs (by simp [hq]), hrest⟩
  have := (Step.step_fields hs).1
  rwa [hstr, hsub] at this

theorem cont_of_c1 {sb : Sub} {b : ℕ} (h : stepSub true Sub.C1 b = some sb) :
    Model.isCont b = true ∧ sb = Sub.PLAIN := by
  rw [stepSub_c1_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem cont_of_c2 {sb : Sub} {b : ℕ} (h : stepSub true Sub.C2 b = some sb) :
    Model.isCont b = true ∧ sb = Sub.C1 := by
  rw [stepSub_c2_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem cont_of_c3 {sb : Sub} {b : ℕ} (h : stepSub true Sub.C3 b = some sb) :
    Model.isCont b = true ∧ sb = Sub.C2 := by
  rw [stepSub_c3_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem cont_of_e0s {sb : Sub} {b : ℕ} (h : stepSub true Sub.E0s b = some sb) :
    Model.isContA0BF b = true ∧ sb = Sub.C1 := by
  rw [stepSub_e0s_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem cont_of_eds {sb : Sub} {b : ℕ} (h : stepSub true Sub.EDs b = some sb) :
    Model.isCont809F b = true ∧ sb = Sub.C1 := by
  rw [stepSub_eds_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem cont_of_f0s {sb : Sub} {b : ℕ} (h : stepSub true Sub.F0s b = some sb) :
    Model.isCont90BF b = true ∧ sb = Sub.C2 := by
  rw [stepSub_f0s_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem cont_of_f4s {sb : Sub} {b : ℕ} (h : stepSub true Sub.F4s b = some sb) :
    Model.isCont808F b = true ∧ sb = Sub.C2 := by
  rw [stepSub_f4s_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem hex_of_h1 {sb : Sub} {b : ℕ} (h : stepSub true Sub.H1 b = some sb) :
    Model.isHex b = true ∧ sb = Sub.H2 := by
  rw [stepSub_h1_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem hex_of_h2 {sb : Sub} {b : ℕ} (h : stepSub true Sub.H2 b = some sb) :
    Model.isHex b = true ∧ sb = Sub.H3 := by
  rw [stepSub_h2_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem hex_of_h3 {sb : Sub} {b : ℕ} (h : stepSub true Sub.H3 b = some sb) :
    Model.isHex b = true ∧ sb = Sub.H4 := by
  rw [stepSub_h3_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem hex_of_h4 {sb : Sub} {b : ℕ} (h : stepSub true Sub.H4 b = some sb) :
    Model.isHex b = true ∧ sb = Sub.PLAIN := by
  rw [stepSub_h4_eq] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem esc_of_esc {sb : Sub} {b : ℕ} (h : stepSub true Sub.ESC b = some sb) :
    (Model.isSimpleEsc b = true ∧ sb = Sub.PLAIN) ∨ (b = lowerU ∧ sb = Sub.H1) := by
  rw [stepSub_esc_eq] at h
  split at h
  · exact Or.inl ⟨by assumption, (Option.some.inj h).symm⟩
  · split at h
    · exact Or.inr ⟨by simpa using (by assumption : (b == lowerU) = true),
        (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

/-! ## The shape of a string body -/

set_option maxHeartbeats 4000000 in
theorem strBody_shape : ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {r rEnd : Regs}, inStr r.st = true → r.sub = Sub.PLAIN →
    runL r L = some rEnd → rEnd.st = St.END →
    ∃ body rest, L = seBytes body ++ (quote :: rest) ∧ (∀ e ∈ body, e.WF) := by
  intro N
  induction N with
  | zero =>
    intro L hL r rEnd hstr hsub h hend
    have hnil : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    exfalso
    rw [RunList.runL_nil, Option.some.injEq] at h
    rw [← h] at hend
    exact inStr_ne_end hstr hend
  | succ N ih =>
    intro L hL r rEnd hstr hsub h hend
    cases L with
    | nil =>
      exfalso
      rw [RunList.runL_nil, Option.some.injEq] at h
      rw [← h] at hend
      exact inStr_ne_end hstr hend
    | cons b L' =>
      simp only [List.length_cons] at hL
      by_cases hq : (b == quote) = true
      · refine ⟨[], L', ?_, by intro e he; simp at he⟩
        rw [show b = quote from by simpa using hq]
        rfl
      · simp only [Bool.not_eq_true] at hq
        obtain ⟨r1, hsub1, hst1, hrest1⟩ := peel_plain hstr hsub hq h
        have hstr1 : inStr r1.st = true := by rw [hst1]; exact hstr
        rw [stepSub_plain_eq] at hsub1
        split_ifs at hsub1 with c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
        · exact absurd c1 (by simp [hq])
        · obtain ⟨body', rest, he, hwf'⟩ :=
            ih L' (by omega) hstr1 (Option.some.inj hsub1).symm hrest1 hend
          refine ⟨SE.plain b :: body', rest, ?_, ?_⟩
          · rw [seBytes_cons, List.append_assoc, ← he]; rfl
          · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
            · exact c2
            · exact hwf' e hem
        · -- a backslash
          have hbs : b = backslash := by simpa using c3
          have hsb1 : r1.sub = Sub.ESC := (Option.some.inj hsub1).symm
          obtain ⟨b2, L2, r2, he2, hsub2, hst2, hrest2⟩ :=
            peel_sub hstr1 (by rw [hsb1]; decide) hrest1 hend
          subst he2
          rw [hsb1] at hsub2
          have hstr2 : inStr r2.st = true := by rw [hst2]; exact hstr1
          simp only [List.length_cons] at hL
          rcases esc_of_esc hsub2 with ⟨hse, hsb2⟩ | ⟨hu, hsb2⟩
          · obtain ⟨body', rest, he, hwf'⟩ := ih L2 (by omega) hstr2 hsb2 hrest2 hend
            refine ⟨SE.esc b2 :: body', rest, ?_, ?_⟩
            · rw [seBytes_cons, List.append_assoc, ← he, hbs]; rfl
            · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
              · exact hse
              · exact hwf' e hem
          · obtain ⟨b3, L3, r3, he3, hsub3, hst3, hrest3⟩ :=
              peel_sub hstr2 (by rw [hsb2]; decide) hrest2 hend
            subst he3
            rw [hsb2] at hsub3
            obtain ⟨hx3, hsb3⟩ := hex_of_h1 hsub3
            have hstr3 : inStr r3.st = true := by rw [hst3]; exact hstr2
            obtain ⟨b4, L4, r4, he4, hsub4, hst4, hrest4⟩ :=
              peel_sub hstr3 (by rw [hsb3]; decide) hrest3 hend
            subst he4
            rw [hsb3] at hsub4
            obtain ⟨hx4, hsb4⟩ := hex_of_h2 hsub4
            have hstr4 : inStr r4.st = true := by rw [hst4]; exact hstr3
            obtain ⟨b5, L5, r5, he5, hsub5, hst5, hrest5⟩ :=
              peel_sub hstr4 (by rw [hsb4]; decide) hrest4 hend
            subst he5
            rw [hsb4] at hsub5
            obtain ⟨hx5, hsb5⟩ := hex_of_h3 hsub5
            have hstr5 : inStr r5.st = true := by rw [hst5]; exact hstr4
            obtain ⟨b6, L6, r6, he6, hsub6, hst6, hrest6⟩ :=
              peel_sub hstr5 (by rw [hsb5]; decide) hrest5 hend
            subst he6
            rw [hsb5] at hsub6
            obtain ⟨hx6, hsb6⟩ := hex_of_h4 hsub6
            have hstr6 : inStr r6.st = true := by rw [hst6]; exact hstr5
            simp only [List.length_cons] at hL
            obtain ⟨body', rest, he, hwf'⟩ := ih L6 (by omega) hstr6 hsb6 hrest6 hend
            refine ⟨SE.hex b3 b4 b5 b6 :: body', rest, ?_, ?_⟩
            · rw [seBytes_cons, List.append_assoc, ← he, hbs, hu]; rfl
            · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
              · exact ⟨hx3, hx4, hx5, hx6⟩
              · exact hwf' e hem
        · -- a 2-byte sequence
          have hsb1 : r1.sub = Sub.C1 := (Option.some.inj hsub1).symm
          obtain ⟨b2, L2, r2, he2, hsub2, hst2, hrest2⟩ :=
            peel_sub hstr1 (by rw [hsb1]; decide) hrest1 hend
          subst he2
          rw [hsb1] at hsub2
          obtain ⟨hc2, hsb2⟩ := cont_of_c1 hsub2
          have hstr2 : inStr r2.st = true := by rw [hst2]; exact hstr1
          simp only [List.length_cons] at hL
          obtain ⟨body', rest, he, hwf'⟩ := ih L2 (by omega) hstr2 hsb2 hrest2 hend
          refine ⟨SE.u2 b b2 :: body', rest, ?_, ?_⟩
          · rw [seBytes_cons, List.append_assoc, ← he]; rfl
          · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
            · exact ⟨c4, hc2⟩
            · exact hwf' e hem
        · -- E0
          have hsb1 : r1.sub = Sub.E0s := (Option.some.inj hsub1).symm
          obtain ⟨b2, L2, r2, he2, hsub2, hst2, hrest2⟩ :=
            peel_sub hstr1 (by rw [hsb1]; decide) hrest1 hend
          subst he2
          rw [hsb1] at hsub2
          obtain ⟨hc2, hsb2⟩ := cont_of_e0s hsub2
          have hstr2 : inStr r2.st = true := by rw [hst2]; exact hstr1
          obtain ⟨b3, L3, r3, he3, hsub3, hst3, hrest3⟩ :=
            peel_sub hstr2 (by rw [hsb2]; decide) hrest2 hend
          subst he3
          rw [hsb2] at hsub3
          obtain ⟨hc3, hsb3⟩ := cont_of_c1 hsub3
          have hstr3 : inStr r3.st = true := by rw [hst3]; exact hstr2
          simp only [List.length_cons] at hL
          obtain ⟨body', rest, he, hwf'⟩ := ih L3 (by omega) hstr3 hsb3 hrest3 hend
          refine ⟨SE.u3 b b2 b3 :: body', rest, ?_, ?_⟩
          · rw [seBytes_cons, List.append_assoc, ← he]; rfl
          · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
            · exact ⟨Or.inl ⟨by simpa using c5, hc2⟩, hc3⟩
            · exact hwf' e hem
        · -- lead3
          have hsb1 : r1.sub = Sub.C2 := (Option.some.inj hsub1).symm
          obtain ⟨b2, L2, r2, he2, hsub2, hst2, hrest2⟩ :=
            peel_sub hstr1 (by rw [hsb1]; decide) hrest1 hend
          subst he2
          rw [hsb1] at hsub2
          obtain ⟨hc2, hsb2⟩ := cont_of_c2 hsub2
          have hstr2 : inStr r2.st = true := by rw [hst2]; exact hstr1
          obtain ⟨b3, L3, r3, he3, hsub3, hst3, hrest3⟩ :=
            peel_sub hstr2 (by rw [hsb2]; decide) hrest2 hend
          subst he3
          rw [hsb2] at hsub3
          obtain ⟨hc3, hsb3⟩ := cont_of_c1 hsub3
          have hstr3 : inStr r3.st = true := by rw [hst3]; exact hstr2
          simp only [List.length_cons] at hL
          obtain ⟨body', rest, he, hwf'⟩ := ih L3 (by omega) hstr3 hsb3 hrest3 hend
          refine ⟨SE.u3 b b2 b3 :: body', rest, ?_, ?_⟩
          · rw [seBytes_cons, List.append_assoc, ← he]; rfl
          · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
            · exact ⟨Or.inr (Or.inl ⟨c6, hc2⟩), hc3⟩
            · exact hwf' e hem
        · -- ED
          have hsb1 : r1.sub = Sub.EDs := (Option.some.inj hsub1).symm
          obtain ⟨b2, L2, r2, he2, hsub2, hst2, hrest2⟩ :=
            peel_sub hstr1 (by rw [hsb1]; decide) hrest1 hend
          subst he2
          rw [hsb1] at hsub2
          obtain ⟨hc2, hsb2⟩ := cont_of_eds hsub2
          have hstr2 : inStr r2.st = true := by rw [hst2]; exact hstr1
          obtain ⟨b3, L3, r3, he3, hsub3, hst3, hrest3⟩ :=
            peel_sub hstr2 (by rw [hsb2]; decide) hrest2 hend
          subst he3
          rw [hsb2] at hsub3
          obtain ⟨hc3, hsb3⟩ := cont_of_c1 hsub3
          have hstr3 : inStr r3.st = true := by rw [hst3]; exact hstr2
          simp only [List.length_cons] at hL
          obtain ⟨body', rest, he, hwf'⟩ := ih L3 (by omega) hstr3 hsb3 hrest3 hend
          refine ⟨SE.u3 b b2 b3 :: body', rest, ?_, ?_⟩
          · rw [seBytes_cons, List.append_assoc, ← he]; rfl
          · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
            · exact ⟨Or.inr (Or.inr ⟨by simpa using c7, hc2⟩), hc3⟩
            · exact hwf' e hem
        · -- F0
          have hsb1 : r1.sub = Sub.F0s := (Option.some.inj hsub1).symm
          obtain ⟨b2, L2, r2, he2, hsub2, hst2, hrest2⟩ :=
            peel_sub hstr1 (by rw [hsb1]; decide) hrest1 hend
          subst he2
          rw [hsb1] at hsub2
          obtain ⟨hc2, hsb2⟩ := cont_of_f0s hsub2
          have hstr2 : inStr r2.st = true := by rw [hst2]; exact hstr1
          obtain ⟨b3, L3, r3, he3, hsub3, hst3, hrest3⟩ :=
            peel_sub hstr2 (by rw [hsb2]; decide) hrest2 hend
          subst he3
          rw [hsb2] at hsub3
          obtain ⟨hc3, hsb3⟩ := cont_of_c2 hsub3
          have hstr3 : inStr r3.st = true := by rw [hst3]; exact hstr2
          obtain ⟨b4, L4, r4, he4, hsub4, hst4, hrest4⟩ :=
            peel_sub hstr3 (by rw [hsb3]; decide) hrest3 hend
          subst he4
          rw [hsb3] at hsub4
          obtain ⟨hc4, hsb4⟩ := cont_of_c1 hsub4
          have hstr4 : inStr r4.st = true := by rw [hst4]; exact hstr3
          simp only [List.length_cons] at hL
          obtain ⟨body', rest, he, hwf'⟩ := ih L4 (by omega) hstr4 hsb4 hrest4 hend
          refine ⟨SE.u4 b b2 b3 b4 :: body', rest, ?_, ?_⟩
          · rw [seBytes_cons, List.append_assoc, ← he]; rfl
          · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
            · exact ⟨Or.inl ⟨by simpa using c8, hc2⟩, hc3, hc4⟩
            · exact hwf' e hem
        · -- lead4
          have hsb1 : r1.sub = Sub.C3 := (Option.some.inj hsub1).symm
          obtain ⟨b2, L2, r2, he2, hsub2, hst2, hrest2⟩ :=
            peel_sub hstr1 (by rw [hsb1]; decide) hrest1 hend
          subst he2
          rw [hsb1] at hsub2
          obtain ⟨hc2, hsb2⟩ := cont_of_c3 hsub2
          have hstr2 : inStr r2.st = true := by rw [hst2]; exact hstr1
          obtain ⟨b3, L3, r3, he3, hsub3, hst3, hrest3⟩ :=
            peel_sub hstr2 (by rw [hsb2]; decide) hrest2 hend
          subst he3
          rw [hsb2] at hsub3
          obtain ⟨hc3, hsb3⟩ := cont_of_c2 hsub3
          have hstr3 : inStr r3.st = true := by rw [hst3]; exact hstr2
          obtain ⟨b4, L4, r4, he4, hsub4, hst4, hrest4⟩ :=
            peel_sub hstr3 (by rw [hsb3]; decide) hrest3 hend
          subst he4
          rw [hsb3] at hsub4
          obtain ⟨hc4, hsb4⟩ := cont_of_c1 hsub4
          have hstr4 : inStr r4.st = true := by rw [hst4]; exact hstr3
          simp only [List.length_cons] at hL
          obtain ⟨body', rest, he, hwf'⟩ := ih L4 (by omega) hstr4 hsb4 hrest4 hend
          refine ⟨SE.u4 b b2 b3 b4 :: body', rest, ?_, ?_⟩
          · rw [seBytes_cons, List.append_assoc, ← he]; rfl
          · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
            · exact ⟨Or.inr (Or.inl ⟨c9, hc2⟩), hc3, hc4⟩
            · exact hwf' e hem
        · -- F4
          have hsb1 : r1.sub = Sub.F4s := (Option.some.inj hsub1).symm
          obtain ⟨b2, L2, r2, he2, hsub2, hst2, hrest2⟩ :=
            peel_sub hstr1 (by rw [hsb1]; decide) hrest1 hend
          subst he2
          rw [hsb1] at hsub2
          obtain ⟨hc2, hsb2⟩ := cont_of_f4s hsub2
          have hstr2 : inStr r2.st = true := by rw [hst2]; exact hstr1
          obtain ⟨b3, L3, r3, he3, hsub3, hst3, hrest3⟩ :=
            peel_sub hstr2 (by rw [hsb2]; decide) hrest2 hend
          subst he3
          rw [hsb2] at hsub3
          obtain ⟨hc3, hsb3⟩ := cont_of_c2 hsub3
          have hstr3 : inStr r3.st = true := by rw [hst3]; exact hstr2
          obtain ⟨b4, L4, r4, he4, hsub4, hst4, hrest4⟩ :=
            peel_sub hstr3 (by rw [hsb3]; decide) hrest3 hend
          subst he4
          rw [hsb3] at hsub4
          obtain ⟨hc4, hsb4⟩ := cont_of_c1 hsub4
          have hstr4 : inStr r4.st = true := by rw [hst4]; exact hstr3
          simp only [List.length_cons] at hL
          obtain ⟨body', rest, he, hwf'⟩ := ih L4 (by omega) hstr4 hsb4 hrest4 hend
          refine ⟨SE.u4 b b2 b3 b4 :: body', rest, ?_, ?_⟩
          · rw [seBytes_cons, List.append_assoc, ← he]; rfl
          · intro e hem; rcases List.mem_cons.mp hem with rfl | hem
            · exact ⟨Or.inr (Or.inr ⟨by simpa using c10, hc2⟩), hc3, hc4⟩
            · exact hwf' e hem

/-! ## The caps of a routed string body -/

theorem sstep_emit_inv {sb : Sub} {h0 : ℕ} {c : Option Claim} {o n b : ℕ} {r' : Regs}
    (he : emitB sb b = true) (hkind : kindOf c = Kind.str ∨ kindOf c = Kind.int)
    (hstep : step (sRegs sb h0 c o n) b = some r') :
    cpB sb h0 b < 0x80 ∧ ∀ k : Claim, c = some k → o < claimCap k := by
  set r : Regs := sRegs sb h0 c o n with hr
  have hstS : r.st = St.STR := rfl
  have hstr : inStr r.st = true := rfl
  have hem : ∀ t : St, (signals r b t).emit = emitB sb b := fun t => by
    rw [sig_emit_inStr hstr]; rfl
  have hve : (signals r b r'.st).vEmit = true := by
    rw [Step.sig_vEmit, Step.strEmitB, Step.digitEmitB, hem r.st, he, hstS]
    simp [St.STR, St.PVAL, St.NSIGN, St.NINT]
  have hwr : (signals r b r'.st).write = true := by
    rw [Step.sig_write, ← Step.sig_vEmit r b r'.st, hve]
    rcases hkind with hk | hk <;> rw [show r.claim = c from rfl, hk] <;> simp
  refine ⟨?_, fun k hk => Step.step_capOk hstep hwr k hk⟩
  have hac := Step.step_asciiOk hstep hwr hstS
  rwa [sig_cp_inStr hstr] at hac

set_option maxHeartbeats 1000000 in
theorem se_str_inv {e : SE} (hwf : e.WF) {c : Option Claim} {o n : ℕ} {r' : Regs}
    (ho : o ≤ ofsMax - 1) (hkind : kindOf c = Kind.str ∨ kindOf c = Kind.int)
    (h : runL (sRegs Sub.PLAIN 0 c o n) e.bytes = some r') :
    e.mcp < 0x80 ∧ (∀ k : Claim, c = some k → o < claimCap k) ∧
      r' = sRegs Sub.PLAIN 0 c (min (o + 1) (ofsMax - 1)) n := by
  have bslash_q : ((backslash == quote) && decide (Sub.PLAIN = Sub.PLAIN)) = false := by decide
  have hfin : ∀ (hm : e.mcp < 0x80) (hc : ∀ k : Claim, c = some k → o < claimCap k),
      r' = sRegs Sub.PLAIN 0 c (min (o + 1) (ofsMax - 1)) n := by
    intro hm hc
    have := (se_run_str (e := e) hwf (h := 0) (c := c) (o := o) (n := n) ho
      (fun _ k hk => hc k hk) (fun _ => hm)).1
    rw [h] at this
    exact Option.some.inj this
  cases e with
  | plain b =>
    have hu : Model.isUnescaped b = true := hwf
    rw [show (SE.plain b).bytes = [b] from rfl, RunList.runL_single] at h
    obtain ⟨ha, hc⟩ := sstep_emit_inv (sb := Sub.PLAIN) (h0 := 0) (by simp [hu]) hkind h
    rw [cpB_plain hu 0] at ha
    exact ⟨ha, hc, hfin ha hc⟩
  | esc b =>
    have hs : Model.isSimpleEsc b = true := hwf
    obtain ⟨s1, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      stepSub_plain_bslash bslash_q (by decide) ho (hexAcc_zero_plain 0 backslash)
    rw [show (SE.esc b).bytes = backslash :: [b] from rfl] at h
    obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
    rw [s1] at hs1
    rw [← Option.some.inj hs1, RunList.runL_single] at hrest
    obtain ⟨ha, hc⟩ := sstep_emit_inv (sb := Sub.ESC) (h0 := 0) (by simp [hs]) hkind hrest
    rw [cpB_esc hs 0] at ha
    exact ⟨ha, hc, hfin ha hc⟩
  | hex a b c' d =>
    obtain ⟨ha4, hb4, hc4, hd4⟩ := hwf
    obtain ⟨s1, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      stepSub_plain_bslash bslash_q (by decide) ho (hexAcc_zero_plain 0 backslash)
    obtain ⟨s2, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      stepSub_esc_u (notQuote_of_sub (by decide) lowerU) (by decide) ho (hexAcc_zero_esc 0 lowerU)
    obtain ⟨s3, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      (stepSub_h1 ha4) (notQuote_of_sub (by decide) a) (by simp) ho (hexAcc_h1 0 a)
    obtain ⟨s4, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 16 * 0 + Model.hexVal a)
      (stepSub_h2 hb4) (notQuote_of_sub (by decide) b) (by simp) ho (hexAcc_h2 _ b)
    obtain ⟨s5, -⟩ := sstep_noemit (c := c) (o := o) (n := n)
      (h := 16 * (16 * 0 + Model.hexVal a) + Model.hexVal b)
      (stepSub_h3 hc4) (notQuote_of_sub (by decide) c') (by simp) ho (hexAcc_h3 _ c')
    rw [show (SE.hex a b c' d).bytes = backslash :: lowerU :: a :: b :: c' :: [d] from rfl] at h
    obtain ⟨r1, hs1, h1⟩ := runL_cons_inv h
    rw [s1] at hs1; rw [← Option.some.inj hs1] at h1
    obtain ⟨r2, hs2, h2⟩ := runL_cons_inv h1
    rw [s2] at hs2; rw [← Option.some.inj hs2] at h2
    obtain ⟨r3, hs3, h3⟩ := runL_cons_inv h2
    rw [s3] at hs3; rw [← Option.some.inj hs3] at h3
    obtain ⟨r4, hs4, h4⟩ := runL_cons_inv h3
    rw [s4] at hs4; rw [← Option.some.inj hs4] at h4
    obtain ⟨r5, hs5, h5⟩ := runL_cons_inv h4
    rw [s5] at hs5; rw [← Option.some.inj hs5, RunList.runL_single] at h5
    obtain ⟨hax, hcx⟩ := sstep_emit_inv (sb := Sub.H4) (by simp [hd4]) hkind h5
    rw [cpB_h4 hd4] at hax
    have hmc : SE.mcp (SE.hex a b c' d) = 16 * (16 * (16 * (16 * 0 + Model.hexVal a)
        + Model.hexVal b) + Model.hexVal c') + Model.hexVal d := by
      simp only [SE.mcp, Serial.hexNum]; ring
    rw [← hmc] at hax
    exact ⟨hax, hcx, hfin hax hcx⟩
  | u2 b0 b1 =>
    obtain ⟨h0', h1'⟩ := hwf
    obtain ⟨s1, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      (stepSub_plain_lead2 h0') (notQuote_of_high (high_of_lead2 h0'))
      (by simp [isUnescaped_false_of_high (high_of_lead2 h0')]) ho (hexAcc_zero_plain 0 b0)
    rw [show (SE.u2 b0 b1).bytes = b0 :: [b1] from rfl] at h
    obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
    rw [s1] at hs1
    rw [← Option.some.inj hs1, RunList.runL_single] at hrest
    obtain ⟨ha, -⟩ := sstep_emit_inv (sb := Sub.C1) (h0 := 0) (by simp [h1']) hkind hrest
    rw [cpB_c1 h1' 0] at ha
    exact absurd ha (by simp [Model.nonAsciiMarker])
  | u3 b0 b1 b2 =>
    obtain ⟨hlead, h2'⟩ := hwf
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
    obtain ⟨s1, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      hsb0 (notQuote_of_high hhigh) (by simp [isUnescaped_false_of_high hhigh]) ho
      (hexAcc_zero_plain 0 b0)
    obtain ⟨s2, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      hsb1 (notQuote_of_sub hsbne b1) hsbe ho hsbh
    rw [show (SE.u3 b0 b1 b2).bytes = b0 :: b1 :: [b2] from rfl] at h
    obtain ⟨r1, hs1, h1⟩ := runL_cons_inv h
    rw [s1] at hs1; rw [← Option.some.inj hs1] at h1
    obtain ⟨r2, hs2, h2⟩ := runL_cons_inv h1
    rw [s2] at hs2; rw [← Option.some.inj hs2, RunList.runL_single] at h2
    obtain ⟨ha, -⟩ := sstep_emit_inv (sb := Sub.C1) (h0 := 0) (by simp [h2']) hkind h2
    rw [cpB_c1 h2' 0] at ha
    exact absurd ha (by simp [Model.nonAsciiMarker])
  | u4 b0 b1 b2 b3 =>
    obtain ⟨hlead, h2', h3'⟩ := hwf
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
    obtain ⟨s1, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      hsb0 (notQuote_of_high hhigh) (by simp [isUnescaped_false_of_high hhigh]) ho
      (hexAcc_zero_plain 0 b0)
    obtain ⟨s2, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      hsb1 (notQuote_of_sub hsbne b1) hsbe ho hsbh
    obtain ⟨s3, -⟩ := sstep_noemit (c := c) (o := o) (n := n) (h := 0)
      (stepSub_c2 h2') (notQuote_of_sub (by decide) b2) (by simp) ho (hexAcc_zero_c2 0 b2)
    rw [show (SE.u4 b0 b1 b2 b3).bytes = b0 :: b1 :: b2 :: [b3] from rfl] at h
    obtain ⟨r1, hs1, h1⟩ := runL_cons_inv h
    rw [s1] at hs1; rw [← Option.some.inj hs1] at h1
    obtain ⟨r2, hs2, h2⟩ := runL_cons_inv h1
    rw [s2] at hs2; rw [← Option.some.inj hs2] at h2
    obtain ⟨r3, hs3, h3⟩ := runL_cons_inv h2
    rw [s3] at hs3; rw [← Option.some.inj hs3, RunList.runL_single] at h3
    obtain ⟨ha, -⟩ := sstep_emit_inv (sb := Sub.C1) (h0 := 0) (by simp [h3']) hkind h3
    rw [cpB_c1 h3' 0] at ha
    exact absurd ha (by simp [Model.nonAsciiMarker])

theorem strBody_caps : ∀ (body : List SE), (∀ e ∈ body, e.WF) →
    ∀ {c : Option Claim} {o n : ℕ} {r1 : Regs},
    (kindOf c = Kind.str ∨ kindOf c = Kind.int) → o ≤ ofsMax - 1 →
    (∀ k : Claim, c = some k → o ≤ claimCap k) →
    runL (sRegs Sub.PLAIN 0 c o n) (seBytes body) = some r1 →
    (∀ e ∈ body, e.mcp < 0x80) ∧ (∀ k : Claim, c = some k → o + body.length ≤ claimCap k) := by
  intro body
  induction body with
  | nil => intro _ c o n r1 _ _ hc0 _; exact ⟨by simp, by simpa using hc0⟩
  | cons e rest ih =>
    intro hwf c o n r1 hkind ho hc0 h
    rw [seBytes_cons, RunList.runL_append] at h
    cases hx : runL (sRegs Sub.PLAIN 0 c o n) e.bytes with
    | none => rw [hx] at h; simp at h
    | some r2 =>
      rw [hx] at h; simp only [Option.bind_some] at h
      obtain ⟨hm, hcp, hr2⟩ := se_str_inv (hwf e (List.mem_cons_self ..)) ho hkind hx
      subst hr2
      have ho' : min (o + 1) (ofsMax - 1) ≤ ofsMax - 1 := by omega
      have hc0' : ∀ k : Claim, c = some k → min (o + 1) (ofsMax - 1) ≤ claimCap k := by
        intro k hk
        have h1 := hcp k hk
        have h2 := RunTheory.claimCap_le k
        simp only [ofsMax] at *
        omega
      obtain ⟨him, hic⟩ := ih (fun x hx' => hwf x (List.mem_cons_of_mem _ hx')) hkind ho' hc0' h
      refine ⟨?_, ?_⟩
      · intro x hx'
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact hm
        · exact him x hx'
      · intro k hk
        have h1 := hcp k hk
        have h2 := hic k hk
        have h3 := RunTheory.claimCap_le k
        simp only [List.length_cons, ofsMax] at *
        omega

/-! ## Digit runs -/

/-- The list does not start with a digit. -/
def NotDigitHead (L : List ℕ) : Prop := ∀ c t, L = c :: t → Model.isDigit c = false

theorem notDigitHead_nil : NotDigitHead [] := by intro c t h; simp at h

/-- The list does not continue a number. -/
def NotNumHead (L : List ℕ) : Prop :=
  ∀ c t, L = c :: t → Model.isDigit c = false ∧ ¬ (c = dot) ∧ Model.isExpLetter c = false

theorem notNumHead_nil : NotNumHead [] := by intro c t h; simp at h

theorem notNum_of_afterValue {b : ℕ} {st' : St} (h : afterValue b = some st') :
    Model.isDigit b = false ∧ ¬ (b = dot) ∧ Model.isExpLetter b = false := by
  rw [afterValue] at h
  split_ifs at h with h1 h2 h3
  · rcases isWs_cases h1 with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, by decide⟩
  · have : b = comma := by simpa using h2
    subst this; exact ⟨by decide, by decide, by decide⟩
  · have : b = rbrace := by simpa using h3
    subst this; exact ⟨by decide, by decide, by decide⟩

theorem notNumHead_aval {L : List ℕ} {r rEnd : Regs} (hst : r.st = St.AVAL)
    (h : runL r L = some rEnd) : NotNumHead L := by
  intro b t hb
  subst hb
  obtain ⟨r1, hs1, -⟩ := runL_cons_inv h
  have hst1 := (Step.step_fields hs1).2.1
  rw [hst, stepSt_aval_eq] at hst1
  exact notNum_of_afterValue hst1

theorem notNumHead_nexp {L : List ℕ} {c : Option Claim} {o n : ℕ} {rEnd : Regs}
    (hnd : NotDigitHead L) (h : runL (nRegs St.NEXP c o n) L = some rEnd) : NotNumHead L := by
  intro b t hb
  have hbd : Model.isDigit b = false := hnd b t hb
  subst hb
  obtain ⟨r1, hs1, -⟩ := runL_cons_inv h
  have hst1 := (Step.step_fields hs1).2.1
  rw [show (nRegs St.NEXP c o n).st = St.NEXP from rfl,
    show (nRegs St.NEXP c o n).claim = c from rfl,
    show decide ((nRegs St.NEXP c o n).sub = Sub.PLAIN) = true from rfl, stepSt_nexp_eq,
    if_neg (by simp [hbd])] at hst1
  exact notNum_of_afterValue hst1

theorem digitsOf_cons (d : ℕ) (ds : List ℕ) :
    digitsOf (d :: ds) = (d + digit0) :: digitsOf ds := by
  simp [digitsOf]

theorem digit_recover {b : ℕ} (h : Model.isDigit b = true) : (b - digit0) + digit0 = b ∧
    b - digit0 ≤ 9 := by
  simp only [Model.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : (0x30 : ℕ) ≤ b := h1
  have h2' : b ≤ 0x39 := h2
  exact ⟨by show b - 0x30 + 0x30 = b; omega, by show b - 0x30 ≤ 9; omega⟩

set_option maxHeartbeats 1000000 in
theorem nint_digits_inv : ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {c : Option Claim} {o n : ℕ} {rEnd : Regs}, o ≤ ofsMax - 1 →
    (∀ k : Claim, c = some k → (kindOf c = Kind.str ∨ kindOf c = Kind.int) → o ≤ claimCap k) →
    runL (nRegs St.NINT c o n) L = some rEnd → rEnd.st = St.END →
    ∃ ds L', (∀ x ∈ ds, x ≤ 9) ∧ L = digitsOf ds ++ L' ∧ NotDigitHead L' ∧
      runL (nRegs St.NINT c (min (o + ds.length) (ofsMax - 1)) n) L' = some rEnd ∧
      (∀ k : Claim, c = some k → (kindOf c = Kind.str ∨ kindOf c = Kind.int) →
        o + ds.length ≤ claimCap k) := by
  intro N
  induction N with
  | zero =>
    intro L hL c o n rEnd ho hc0 h hend
    have hnil : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    exact ⟨[], [], by simp, by simp [digitsOf], notDigitHead_nil,
      by rw [List.length_nil, Nat.add_zero, Nat.min_eq_left ho]; exact h,
      by intro k hk hkk; simpa using hc0 k hk hkk⟩
  | succ N ih =>
    intro L hL c o n rEnd ho hc0 h hend
    cases L with
    | nil =>
      exact ⟨[], [], by simp, by simp [digitsOf], notDigitHead_nil,
        by rw [List.length_nil, Nat.add_zero, Nat.min_eq_left ho]; exact h,
        by intro k hk hkk; simpa using hc0 k hk hkk⟩
    | cons b L' =>
      simp only [List.length_cons] at hL
      by_cases hd : Model.isDigit b = true
      · obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
        have hdE : dEmit St.NINT b = true := dEmit_of_digit hd (Or.inr (Or.inr rfl))
        have hcapk : (kindOf c = Kind.str ∨ kindOf c = Kind.int) →
            ∀ k : Claim, c = some k → o < claimCap k := by
          intro hk k hck
          have hve : (signals (nRegs St.NINT c o n) b r1.st).vEmit = true := by
            rw [Step.sig_vEmit, Step.strEmitB, Step.digitEmitB]
            simp only [nRegs]
            simp [hd, St.NINT, St.STR, St.PVAL, St.NSIGN]
          have hwr : (signals (nRegs St.NINT c o n) b r1.st).write = true := by
            rw [Step.sig_write, ← Step.sig_vEmit _ b r1.st, hve]
            rcases hk with hk | hk <;> rw [show (nRegs St.NINT c o n).claim = c from rfl, hk] <;>
              simp
          exact Step.step_capOk hs1 hwr k hck
        obtain ⟨s1, -⟩ := nstepE (s := St.NINT) (s' := St.NINT) (c := c) (o := o)
          (o' := min (o + 1) (ofsMax - 1)) (n := n) (by decide) (by decide)
          (by rw [stepSt_nint_eq, if_pos hd]) hdE
          (fun hk k hck => hcapk hk k hck) (by rw [if_pos (by decide)])
        rw [s1] at hs1
        rw [← Option.some.inj hs1] at hrest
        have ho' : min (o + 1) (ofsMax - 1) ≤ ofsMax - 1 := by omega
        have hc0' : ∀ k : Claim, c = some k →
            (kindOf c = Kind.str ∨ kindOf c = Kind.int) → min (o + 1) (ofsMax - 1)
              ≤ claimCap k := by
          intro k hk hkind
          have h1 := hcapk hkind k hk
          have h2 := RunTheory.claimCap_le k
          simp only [ofsMax] at *
          omega
        obtain ⟨ds, L2, hds, heq, hnd, hrun, hcap⟩ := ih L' (by omega) ho' hc0' hrest hend
        obtain ⟨hrec, hle9⟩ := digit_recover hd
        refine ⟨(b - digit0) :: ds, L2, ?_, ?_, hnd, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hle9
          · exact hds x hx
        · rw [digitsOf_cons, hrec, heq, List.cons_append]
        · rw [show ((b - digit0) :: ds).length = ds.length + 1 from rfl]
          have : min (min (o + 1) (ofsMax - 1) + ds.length) (ofsMax - 1)
              = min (o + (ds.length + 1)) (ofsMax - 1) := by simp only [ofsMax]; omega
          rw [← this]
          exact hrun
        · intro k hck hk
          have h1 := hcapk hk k hck
          have h2 := hcap k hck hk
          have h3 := RunTheory.claimCap_le k
          simp only [List.length_cons, ofsMax] at *
          omega
      · simp only [Bool.not_eq_true] at hd
        exact ⟨[], b :: L', by simp, by simp [digitsOf],
          (by intro cc t he; rw [List.cons.injEq] at he; rw [← he.1]; exact hd),
          by rw [List.length_nil, Nat.add_zero, Nat.min_eq_left ho]; exact h,
          by intro k hk hkk; simpa using hc0 k hk hkk⟩

set_option maxHeartbeats 1000000 in
theorem quiet_digits_inv {s : St} (hs : s = St.NFRAC ∨ s = St.NEXP) :
    ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {c : Option Claim} {o n : ℕ} {rEnd : Regs}, o ≤ ofsMax - 1 →
    runL (nRegs s c o n) L = some rEnd → rEnd.st = St.END →
    ∃ ds L', (∀ x ∈ ds, x ≤ 9) ∧ L = digitsOf ds ++ L' ∧ NotDigitHead L' ∧
      runL (nRegs s c o n) L' = some rEnd := by
  intro N
  induction N with
  | zero =>
    intro L hL c o n rEnd ho h hend
    have hnil : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    exact ⟨[], [], by simp, by simp [digitsOf], notDigitHead_nil, h⟩
  | succ N ih =>
    intro L hL c o n rEnd ho h hend
    cases L with
    | nil => exact ⟨[], [], by simp, by simp [digitsOf], notDigitHead_nil, h⟩
    | cons b L' =>
      simp only [List.length_cons] at hL
      by_cases hd : Model.isDigit b = true
      · obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
        have hstep : stepSt (kindOf c) true s b = some s := by
          rcases hs with rfl | rfl
          · rw [stepSt_nfrac_eq, if_pos hd]
          · rw [stepSt_nexp_eq, if_pos hd]
        obtain ⟨s1, -⟩ := nstepQ (s := s) (s' := s) (c := c) (o := o) (o' := o) (n := n)
          (by rcases hs with rfl | rfl <;> decide) (by rcases hs with rfl | rfl <;> decide)
          hstep (dEmit_quiet (by rcases hs with rfl | rfl <;> simp))
          (by rcases hs with rfl | rfl <;> simp [St.NFRAC, St.NEXP, St.PVAL])
          (by rcases hs with rfl | rfl <;> simp [St.NFRAC, St.NEXP, St.T3])
          (by rw [if_pos (by rcases hs with rfl | rfl <;> decide)]; exact Nat.min_eq_left ho)
        rw [s1] at hs1
        rw [← Option.some.inj hs1] at hrest
        obtain ⟨ds, L2, hds, heq, hnd, hrun⟩ := ih L' (by omega) ho hrest hend
        obtain ⟨hrec, hle9⟩ := digit_recover hd
        refine ⟨(b - digit0) :: ds, L2, ?_, ?_, hnd, hrun⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hle9
          · exact hds x hx
        · rw [digitsOf_cons, hrec, heq, List.cons_append]
      · simp only [Bool.not_eq_true] at hd
        exact ⟨[], b :: L', by simp, by simp [digitsOf],
          (by intro cc t he; rw [List.cons.injEq] at he; rw [← he.1]; exact hd), h⟩

/-! ## Peeling inside a number -/

theorem peel_num {s : St} {c : Option Claim} {o n : ℕ} {L : List ℕ} {rEnd : Regs}
    (hne : s ≠ St.END) (h : runL (nRegs s c o n) L = some rEnd) (hend : rEnd.st = St.END) :
    ∃ b L' r1, L = b :: L' ∧ step (nRegs s c o n) b = some r1 ∧ runL r1 L' = some rEnd := by
  cases L with
  | nil =>
    exfalso
    rw [RunList.runL_nil, Option.some.injEq] at h
    rw [← h] at hend
    exact hne hend
  | cons b L' =>
    obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
    exact ⟨b, L', r1, rfl, hs1, hrest⟩

theorem stepSt_num_tail_inv {kind : Kind} {sp : Bool} {s : St}
    (hs : s = St.NZERO ∨ s = St.NINT) {b : ℕ} {st' : St} (hnd : Model.isDigit b = false)
    (h : stepSt kind sp s b = some st') :
    ((b = dot ∧ kind = Kind.unk) ∧ st' = St.NDOT) ∨
    ((Model.isExpLetter b = true ∧ kind = Kind.unk) ∧ st' = St.NE) ∨
    afterValue b = some st' := by
  rcases hs with rfl | rfl
  · rw [stepSt_nzero_eq] at h
    split_ifs at h with c1 c2
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c1
      exact Or.inl ⟨c1, (Option.some.inj h).symm⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at c2
      exact Or.inr (Or.inl ⟨c2, (Option.some.inj h).symm⟩)
    · exact Or.inr (Or.inr h)
  · rw [stepSt_nint_eq, if_neg (by simp [hnd])] at h
    split_ifs at h with c1 c2
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c1
      exact Or.inl ⟨c1, (Option.some.inj h).symm⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at c2
      exact Or.inr (Or.inl ⟨c2, (Option.some.inj h).symm⟩)
    · exact Or.inr (Or.inr h)

theorem stepSt_nfrac_inv {kind : Kind} {sp : Bool} {b : ℕ} {st' : St}
    (hnd : Model.isDigit b = false) (h : stepSt kind sp St.NFRAC b = some st') :
    (Model.isExpLetter b = true ∧ st' = St.NE) ∨ afterValue b = some st' := by
  rw [stepSt_nfrac_eq, if_neg (by simp [hnd])] at h
  split_ifs at h with c1
  · exact Or.inl ⟨c1, (Option.some.inj h).symm⟩
  · exact Or.inr h

theorem stepSt_ndot_inv {kind : Kind} {sp : Bool} {b : ℕ} {st' : St}
    (h : stepSt kind sp St.NDOT b = some st') : Model.isDigit b = true ∧ st' = St.NFRAC := by
  rw [stepSt_ndot_eq] at h
  split_ifs at h with c1
  · exact ⟨c1, (Option.some.inj h).symm⟩

theorem stepSt_ne_inv {kind : Kind} {sp : Bool} {b : ℕ} {st' : St}
    (h : stepSt kind sp St.NE b = some st') :
    (Model.isSign b = true ∧ st' = St.NESIGN) ∨ (Model.isDigit b = true ∧ st' = St.NEXP) := by
  rw [stepSt_ne_eq] at h
  split_ifs at h with c1 c2
  · exact Or.inl ⟨c1, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨c2, (Option.some.inj h).symm⟩

theorem stepSt_nesign_inv {kind : Kind} {sp : Bool} {b : ℕ} {st' : St}
    (h : stepSt kind sp St.NESIGN b = some st') : Model.isDigit b = true ∧ st' = St.NEXP := by
  rw [stepSt_nesign_eq] at h
  split_ifs at h with c1
  · exact ⟨c1, (Option.some.inj h).symm⟩

theorem stepSt_pval_num_inv {c : Option Claim} {b : ℕ} {st' : St}
    (hd : Model.isDigit b = true) (h : stepSt (kindOf c) true St.PVAL b = some st') :
    (kindOf c = Kind.int ∨ kindOf c = Kind.unk) ∧
      ((b = digit0 ∧ st' = St.NZERO) ∨ (Model.isDigitNz b = true ∧ st' = St.NINT)) := by
  have hb : 0x30 ≤ b ∧ b ≤ 0x39 := by
    simpa only [Model.isDigit, Bool.and_eq_true, decide_eq_true_eq] using hd
  have hnws : Model.isWs b = false := by
    simp only [Model.isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
      [show b ≠ 0x20; show b ≠ 0x09; show b ≠ 0x0A; show b ≠ 0x0D] <;> omega
  have hnq : (b == quote) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x22; omega
  have hnm : (b == minus) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x2D; omega
  rw [stepSt_pval_eq, if_neg (by simp [hnws]), if_neg (by simp [hnq]),
    if_neg (by simp [hnm])] at h
  split_ifs at h with c1 c2 c3 c4 c5
  · simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at c1
    exact ⟨c1.2, Or.inl ⟨c1.1, (Option.some.inj h).symm⟩⟩
  · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at c2
    exact ⟨c2.2, Or.inr ⟨c2.1, (Option.some.inj h).symm⟩⟩
  · exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at c3
    have : b = 0x74 := c3.1
    omega
  · exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at c4
    have : b = 0x66 := c4.1
    omega
  · exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at c5
    have : b = 0x6E := c5.1
    omega

theorem stepSt_nsign_num_inv {kind : Kind} {sp : Bool} {b : ℕ} {st' : St}
    (h : stepSt kind sp St.NSIGN b = some st') :
    (b = digit0 ∧ st' = St.NZERO) ∨ (Model.isDigitNz b = true ∧ st' = St.NINT) := by
  rw [stepSt_nsign_eq] at h
  split_ifs at h with c1 c2
  · exact Or.inl ⟨by simpa using c1, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨c2, (Option.some.inj h).symm⟩

/-! ## The exponent and the fractional part -/

theorem nzero_notDigit {kind : Kind} {sp : Bool} {b : ℕ} {st' : St}
    (h : stepSt kind sp St.NZERO b = some st') : Model.isDigit b = false := by
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  have hb : 0x30 ≤ b ∧ b ≤ 0x39 := by
    simpa only [Model.isDigit, Bool.and_eq_true, decide_eq_true_eq] using hc
  have hdot : (b == dot) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; show b ≠ 0x2E; omega
  have hexp : Model.isExpLetter b = false := by
    simp only [Model.isExpLetter, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    constructor <;> [show b ≠ 0x65; show b ≠ 0x45] <;> omega
  have hws : Model.isWs b = false := by
    simp only [Model.isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
      [show b ≠ 0x20; show b ≠ 0x09; show b ≠ 0x0A; show b ≠ 0x0D] <;> omega
  have hav : afterValue b = none := by
    rw [afterValue, if_neg (by simp [hws]),
      if_neg (show ¬ ((b == comma) = true) from by
        simp only [beq_iff_eq]; show ¬ (b = 0x2C); omega),
      if_neg (show ¬ ((b == rbrace) = true) from by
        simp only [beq_iff_eq]; show ¬ (b = 0x7D); omega)]
  rw [stepSt_nzero_eq, if_neg (by simp [hdot]), if_neg (by simp [hexp]), hav] at h
  exact absurd h (by simp)

theorem exp_inv : ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {s2 : St}, (s2 = St.NZERO ∨ s2 = St.NINT ∨ s2 = St.NFRAC) →
    ∀ {c : Option Claim} {o n : ℕ} {rEnd : Regs}, o ≤ ofsMax - 1 → NotDigitHead L →
    ((s2 = St.NZERO ∨ s2 = St.NINT) → ∀ cc t, L = cc :: t → ¬ (cc = dot)) →
    runL (nRegs s2 c o n) L = some rEnd → rEnd.st = St.END →
    ∃ (ex : Option SExp) (rest : List ℕ),
      (match ex with
        | none => True
        | some e => (e.letter = lowerE ∨ e.letter = upperE) ∧
            (match e.sign with | none => True | some sg => sg = plus ∨ sg = minus) ∧
            e.digits ≠ [] ∧ ∀ x ∈ e.digits, x ≤ 9) ∧
      (ex ≠ none → (s2 = St.NZERO ∨ s2 = St.NINT) → kindOf c = Kind.unk) ∧
      NotNumHead rest ∧
      L = (ex.map SExp.bytes).getD [] ++ rest := by
  intro N L hL s2 hs2 c o n rEnd ho hnd hnodot h hend
  have hne : s2 ≠ St.END := by rcases hs2 with rfl | rfl | rfl <;> decide
  obtain ⟨b, L', r1, rfl, hs1, hrest⟩ := peel_num hne h hend
  have hst1 := (Step.step_fields hs1).2.1
  rw [show (nRegs s2 c o n).st = s2 from rfl, show (nRegs s2 c o n).claim = c from rfl,
    show decide ((nRegs s2 c o n).sub = Sub.PLAIN) = true from rfl] at hst1
  have hbd : Model.isDigit b = false := hnd b L' rfl
  have hcase : (Model.isExpLetter b = true ∧ r1.st = St.NE ∧
        ((s2 = St.NZERO ∨ s2 = St.NINT) → kindOf c = Kind.unk)) ∨
      afterValue b = some r1.st := by
    rcases hs2 with hh | hh | hh
    · rw [hh] at hst1
      rcases stepSt_num_tail_inv (Or.inl rfl) hbd hst1 with ⟨⟨hd, -⟩, -⟩ | ⟨⟨he, hk⟩, hst⟩ | hav
      · exact absurd hd (hnodot (Or.inl hh) b L' rfl)
      · exact Or.inl ⟨he, hst, fun _ => hk⟩
      · exact Or.inr hav
    · rw [hh] at hst1
      rcases stepSt_num_tail_inv (Or.inr rfl) hbd hst1 with ⟨⟨hd, -⟩, -⟩ | ⟨⟨he, hk⟩, hst⟩ | hav
      · exact absurd hd (hnodot (Or.inr hh) b L' rfl)
      · exact Or.inl ⟨he, hst, fun _ => hk⟩
      · exact Or.inr hav
    · rw [hh] at hst1
      rcases stepSt_nfrac_inv hbd hst1 with ⟨he, hst⟩ | hav
      · refine Or.inl ⟨he, hst, ?_⟩
        intro hx
        rw [hh] at hx
        rcases hx with hx | hx <;> exact absurd hx (by decide)
      · exact Or.inr hav
  rcases hcase with ⟨hexl, hst1', hunk⟩ | hav
  · -- the exponent starts here
    have hinval : Step.inValP s2 = true := by rcases hs2 with rfl | rfl | rfl <;> decide
    obtain ⟨sE, -⟩ := nstepQ (s := s2) (s' := St.NE) (c := c) (o := o) (o' := o) (n := n)
      (by rcases hs2 with rfl | rfl | rfl <;> decide) (by decide) (by rw [← hst1']; exact hst1)
      (dEmit_of_notDigit hbd)
      (by rcases hs2 with rfl | rfl | rfl <;> simp [St.NZERO, St.NINT, St.NFRAC, St.PVAL])
      (by rcases hs2 with rfl | rfl | rfl <;> simp [St.NZERO, St.NINT, St.NFRAC, St.T3])
      (by rw [if_pos hinval]; exact Nat.min_eq_left ho)
    rw [sE] at hs1
    rw [← Option.some.inj hs1] at hrest
    -- from NE: an optional sign then the digits
    obtain ⟨b2, L2, r2, rfl, hs2', hrest2⟩ := peel_num (s := St.NE) (by decide) hrest hend
    have hst2 := (Step.step_fields hs2').2.1
    rw [show (nRegs St.NE c o n).st = St.NE from rfl,
      show (nRegs St.NE c o n).claim = c from rfl,
      show decide ((nRegs St.NE c o n).sub = Sub.PLAIN) = true from rfl] at hst2
    rcases stepSt_ne_inv hst2 with ⟨hsg, hst2'⟩ | ⟨hdg, hst2'⟩
    · -- a sign
      obtain ⟨sS, -⟩ := nstepQ (s := St.NE) (s' := St.NESIGN) (c := c) (o := o) (o' := o) (n := n)
        (by decide) (by decide) (by rw [← hst2']; exact hst2)
        (dEmit_of_notDigit (by
          simp only [Model.isSign, Bool.or_eq_true, beq_iff_eq] at hsg
          rcases hsg with rfl | rfl <;> decide))
        (by simp [St.NE, St.PVAL]) (by simp [St.NE, St.T3])
        (by rw [if_pos (by decide)]; exact Nat.min_eq_left ho)
      rw [sS] at hs2'
      rw [← Option.some.inj hs2'] at hrest2
      obtain ⟨b3, L3, r3, rfl, hs3, hrest3⟩ := peel_num (s := St.NESIGN) (by decide) hrest2 hend
      have hst3 := (Step.step_fields hs3).2.1
      rw [show (nRegs St.NESIGN c o n).st = St.NESIGN from rfl,
        show (nRegs St.NESIGN c o n).claim = c from rfl,
        show decide ((nRegs St.NESIGN c o n).sub = Sub.PLAIN) = true from rfl] at hst3
      obtain ⟨hdg3, hst3'⟩ := stepSt_nesign_inv hst3
      obtain ⟨sX, -⟩ := nstepQ (s := St.NESIGN) (s' := St.NEXP) (c := c) (o := o) (o' := o)
        (n := n) (by decide) (by decide) (by rw [← hst3']; exact hst3)
        (dEmit_quiet (by simp)) (by simp [St.NESIGN, St.PVAL]) (by simp [St.NESIGN, St.T3])
        (by rw [if_pos (by decide)]; exact Nat.min_eq_left ho)
      rw [sX] at hs3
      rw [← Option.some.inj hs3] at hrest3
      obtain ⟨ds, L4, hds, heq, hnd4, hrun4⟩ :=
        quiet_digits_inv (s := St.NEXP) (Or.inr rfl) N L3 (by
          simp only [List.length_cons] at hL; omega) ho hrest3 hend
      obtain ⟨hrec3, hle3⟩ := digit_recover hdg3
      refine ⟨some ⟨b, some b2, (b3 - digit0) :: ds⟩, L4, ?_, ?_, notNumHead_nexp hnd4 hrun4, ?_⟩
      · refine ⟨by simpa only [Model.isExpLetter, Bool.or_eq_true, beq_iff_eq] using hexl, ?_,
          by simp, ?_⟩
        · simpa only [Model.isSign, Bool.or_eq_true, beq_iff_eq] using hsg
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hle3
          · exact hds x hx
      · intro _ hh; exact hunk hh
      · rw [heq]
        simp only [Option.map_some, Option.getD_some, SExp.bytes, digitsOf_cons, hrec3,
          digitsOf, List.map_cons]
        simp
    · -- no sign
      obtain ⟨sX, -⟩ := nstepQ (s := St.NE) (s' := St.NEXP) (c := c) (o := o) (o' := o)
        (n := n) (by decide) (by decide) (by rw [← hst2']; exact hst2)
        (dEmit_quiet (by simp)) (by simp [St.NE, St.PVAL]) (by simp [St.NE, St.T3])
        (by rw [if_pos (by decide)]; exact Nat.min_eq_left ho)
      rw [sX] at hs2'
      rw [← Option.some.inj hs2'] at hrest2
      obtain ⟨ds, L4, hds, heq, hnd4, hrun4⟩ :=
        quiet_digits_inv (s := St.NEXP) (Or.inr rfl) N L2 (by
          simp only [List.length_cons] at hL; omega) ho hrest2 hend
      obtain ⟨hrec2, hle2⟩ := digit_recover hdg
      refine ⟨some ⟨b, none, (b2 - digit0) :: ds⟩, L4, ?_, ?_, notNumHead_nexp hnd4 hrun4, ?_⟩
      · refine ⟨by simpa only [Model.isExpLetter, Bool.or_eq_true, beq_iff_eq] using hexl,
          trivial, by simp, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hle2
        · exact hds x hx
      · intro _ hh; exact hunk hh
      · rw [heq]
        simp only [Option.map_some, Option.getD_some, SExp.bytes, digitsOf_cons, hrec2,
          digitsOf, List.map_cons]
        simp
  · -- no exponent
    refine ⟨none, b :: L', trivial, by intro hx; exact absurd rfl hx, ?_, by simp⟩
    intro cc t hcc
    rw [List.cons.injEq] at hcc
    rw [← hcc.1]
    exact notNum_of_afterValue hav

/-! ## The tail of a number -/

set_option maxHeartbeats 1000000 in
theorem num_tail_inv : ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {s1 : St}, (s1 = St.NZERO ∨ s1 = St.NINT) →
    ∀ {c : Option Claim} {o n : ℕ} {rEnd : Regs}, o ≤ ofsMax - 1 → NotDigitHead L →
    runL (nRegs s1 c o n) L = some rEnd → rEnd.st = St.END →
    ∃ (frac : List ℕ) (ex : Option SExp) (rest : List ℕ),
      (∀ x ∈ frac, x ≤ 9) ∧
      (match ex with
        | none => True
        | some e => (e.letter = lowerE ∨ e.letter = upperE) ∧
            (match e.sign with | none => True | some sg => sg = plus ∨ sg = minus) ∧
            e.digits ≠ [] ∧ ∀ x ∈ e.digits, x ≤ 9) ∧
      ((frac ≠ [] ∨ ex ≠ none) → kindOf c = Kind.unk) ∧ NotNumHead rest ∧
      L = (if frac = [] then [] else dot :: digitsOf frac)
            ++ ((ex.map SExp.bytes).getD [] ++ rest) := by
  intro N L hL s1 hs1 c o n rEnd ho hnd h hend
  have hne : s1 ≠ St.END := by rcases hs1 with rfl | rfl <;> decide
  have hinval : Step.inValP s1 = true := by rcases hs1 with rfl | rfl <;> decide
  by_cases hdot : ∃ t, L = dot :: t
  · obtain ⟨t, rfl⟩ := hdot
    obtain ⟨b, L', r1, he1, hs1', hrest⟩ := peel_num hne h hend
    rw [List.cons.injEq] at he1
    obtain ⟨rfl, rfl⟩ := he1
    have hst1 := (Step.step_fields hs1').2.1
    rw [show (nRegs s1 c o n).st = s1 from rfl, show (nRegs s1 c o n).claim = c from rfl,
      show decide ((nRegs s1 c o n).sub = Sub.PLAIN) = true from rfl] at hst1
    have hbd : Model.isDigit dot = false := by decide
    have hcase : kindOf c = Kind.unk ∧ r1.st = St.NDOT := by
      rcases stepSt_num_tail_inv hs1 hbd hst1 with ⟨⟨-, hk⟩, hst⟩ | ⟨⟨he, -⟩, -⟩ | hav
      · exact ⟨hk, hst⟩
      · exact absurd he (by decide)
      · exact absurd hav (by rw [show afterValue dot = none from by decide]; simp)
    obtain ⟨hunk, hst1'⟩ := hcase
    obtain ⟨sD, -⟩ := nstepQ (s := s1) (s' := St.NDOT) (c := c) (o := o) (o' := o) (n := n)
      (by rcases hs1 with rfl | rfl <;> decide) (by decide) (by rw [← hst1']; exact hst1)
      (dEmit_of_notDigit hbd)
      (by rcases hs1 with rfl | rfl <;> simp [St.NZERO, St.NINT, St.PVAL])
      (by rcases hs1 with rfl | rfl <;> simp [St.NZERO, St.NINT, St.T3])
      (by rw [if_pos hinval]; exact Nat.min_eq_left ho)
    rw [sD] at hs1'
    rw [← Option.some.inj hs1'] at hrest
    obtain ⟨d, L2, r2, rfl, hs2, hrest2⟩ := peel_num (s := St.NDOT) (by decide) hrest hend
    have hst2 := (Step.step_fields hs2).2.1
    rw [show (nRegs St.NDOT c o n).st = St.NDOT from rfl,
      show (nRegs St.NDOT c o n).claim = c from rfl,
      show decide ((nRegs St.NDOT c o n).sub = Sub.PLAIN) = true from rfl] at hst2
    obtain ⟨hdd, hst2'⟩ := stepSt_ndot_inv hst2
    obtain ⟨sF, -⟩ := nstepQ (s := St.NDOT) (s' := St.NFRAC) (c := c) (o := o) (o' := o) (n := n)
      (by decide) (by decide) (by rw [← hst2']; exact hst2) (dEmit_quiet (by simp))
      (by simp [St.NDOT, St.PVAL]) (by simp [St.NDOT, St.T3])
      (by rw [if_pos (by decide)]; exact Nat.min_eq_left ho)
    rw [sF] at hs2
    rw [← Option.some.inj hs2] at hrest2
    simp only [List.length_cons] at hL
    obtain ⟨ds, L3, hds, heq3, hnd3, hrun3⟩ :=
      quiet_digits_inv (s := St.NFRAC) (Or.inl rfl) N L2 (by omega) ho hrest2 hend
    obtain ⟨ex, rest, hexwf, -, hnn3, hex3⟩ :=
      exp_inv N L3 (by
        have : L3.length ≤ L2.length := by rw [heq3]; simp
        omega) (Or.inr (Or.inr rfl)) ho hnd3
        (by intro hx; rcases hx with hx | hx <;> exact absurd hx (by decide)) hrun3 hend
    obtain ⟨hrecd, hled⟩ := digit_recover hdd
    refine ⟨(d - digit0) :: ds, ex, rest, ?_, hexwf, fun _ => hunk, hnn3, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hled
      · exact hds x hx
    · rw [if_neg (by simp), heq3, hex3, digitsOf_cons, hrecd]
      simp
  · push_neg at hdot
    have hnodot : (s1 = St.NZERO ∨ s1 = St.NINT) → ∀ cc t, L = cc :: t → ¬ (cc = dot) := by
      intro _ cc t he hcc
      exact hdot t (by rw [he, hcc])
    obtain ⟨ex, rest, hexwf, hunk, hnn, hex⟩ :=
      exp_inv N L hL (by rcases hs1 with rfl | rfl <;> simp) ho hnd hnodot h hend
    refine ⟨[], ex, rest, by simp, hexwf, ?_, hnn, by rw [if_pos rfl, hex]; simp⟩
    intro hx
    rcases hx with hx | hx
    · exact absurd rfl hx
    · exact hunk hx hs1

/-! ## A whole number -/

theorem digitNz_recover {b : ℕ} (h : Model.isDigitNz b = true) :
    (b - digit0) + digit0 = b ∧ 1 ≤ b - digit0 ∧ b - digit0 ≤ 9 ∧ Model.isDigit b = true := by
  have hb : 0x30 < b ∧ b ≤ 0x39 := by
    simpa only [Model.isDigitNz, Bool.and_eq_true, decide_eq_true_eq] using h
  refine ⟨by show b - 0x30 + 0x30 = b; omega, by show 1 ≤ b - 0x30; omega,
    by show b - 0x30 ≤ 9; omega, ?_⟩
  simp only [Model.isDigit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by show (0x30 : ℕ) ≤ b; omega, by show b ≤ 0x39; omega⟩

set_option maxHeartbeats 1000000 in
theorem num_inv : ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {s0 : St}, (s0 = St.PVAL ∨ s0 = St.NSIGN) →
    ∀ {c : Option Claim} {n : ℕ} {rEnd : Regs} {b : ℕ},
    (kindOf c = Kind.int ∨ kindOf c = Kind.unk) → Model.isDigit b = true →
    runL (nRegs s0 c 0 n) (b :: L) = some rEnd → rEnd.st = St.END →
    ∃ (nm : SNum) (rest : List ℕ),
      nm.neg = false ∧ nm.WF ∧ b :: L = nm.bytes ++ rest ∧
      (kindOf c = Kind.int → nm.frac = [] ∧ nm.exp = none) ∧
      (∀ k : Claim, c = some k → nm.ints.length ≤ claimCap k) ∧ NotNumHead rest := by
  intro N L hL s0 hs0 c n rEnd b hkind hd h hend
  obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
  have hst1 := (Step.step_fields hs1).2.1
  rw [show (nRegs s0 c 0 n).st = s0 from rfl, show (nRegs s0 c 0 n).claim = c from rfl,
    show decide ((nRegs s0 c 0 n).sub = Sub.PLAIN) = true from rfl] at hst1
  have hs0' : s0 = St.PVAL ∨ s0 = St.NSIGN ∨ s0 = St.NINT := by
    rcases hs0 with h1 | h1 <;> tauto
  have hdE : dEmit s0 b = true := dEmit_of_digit hd hs0'
  have hkc : ∀ k : Claim, c = some k → (kindOf c = Kind.str ∨ kindOf c = Kind.int) := by
    intro k hk
    rcases hkind with hh | hh
    · exact Or.inr hh
    · exfalso
      rw [hk] at hh
      have : ∀ k' : Claim, kindOf (some k') ≠ Kind.unk := by decide
      exact this k hh
  have hcap0 : ∀ k : Claim, c = some k → 0 < claimCap k := by
    intro k hk
    have hve : (signals (nRegs s0 c 0 n) b r1.st).vEmit = true := by
      rw [Step.sig_vEmit, Step.strEmitB, Step.digitEmitB]
      simp only [nRegs]
      rcases hs0 with rfl | rfl <;> simp [hd, St.PVAL, St.NSIGN, St.STR, St.NINT]
    have hwr : (signals (nRegs s0 c 0 n) b r1.st).write = true := by
      rw [Step.sig_write, ← Step.sig_vEmit _ b r1.st, hve]
      rcases hkc k hk with hh | hh <;>
        rw [show (nRegs s0 c 0 n).claim = c from rfl, hh] <;> simp
    exact Step.step_capOk hs1 hwr k hk
  have hcls : (b = digit0 ∧ r1.st = St.NZERO) ∨ (Model.isDigitNz b = true ∧ r1.st = St.NINT) := by
    rcases hs0 with hh | hh
    · rw [hh] at hst1; exact (stepSt_pval_num_inv hd hst1).2
    · rw [hh] at hst1; exact stepSt_nsign_num_inv hst1
  rcases hcls with ⟨hb0, hst⟩ | ⟨hnz, hst⟩
  · subst hb0
    obtain ⟨sZ, -⟩ := nstepE (s := s0) (s' := St.NZERO) (c := c) (o := 0) (o' := 1) (n := n)
      (by rcases hs0 with rfl | rfl <;> decide) (by decide) (by rw [← hst]; exact hst1) hdE
      (fun _ k hk => hcap0 k hk) (by simp)
    rw [sZ] at hs1
    rw [← Option.some.inj hs1] at hrest
    have hndL : NotDigitHead L := by
      intro cc t hcc
      by_contra hcd
      simp only [Bool.not_eq_false] at hcd
      subst hcc
      obtain ⟨r2, hs2, -⟩ := runL_cons_inv hrest
      have hst2 := (Step.step_fields hs2).2.1
      rw [show (nRegs St.NZERO c 1 n).st = St.NZERO from rfl,
        show (nRegs St.NZERO c 1 n).claim = c from rfl,
        show decide ((nRegs St.NZERO c 1 n).sub = Sub.PLAIN) = true from rfl] at hst2
      exact absurd (nzero_notDigit hst2) (by simp [hcd])
    obtain ⟨frac, ex, rest, hfr, hexwf, hunk, hnn, heq⟩ :=
      num_tail_inv N L (by omega) (Or.inl rfl) (by simp only [ofsMax]; omega) hndL hrest hend
    refine ⟨⟨false, [0], frac, ex⟩, rest, rfl, ⟨Or.inl rfl, hfr, hexwf⟩, ?_, ?_, ?_, hnn⟩
    · rw [SerParse.snum_bytes_append]
      simp only [if_neg (show ¬ (false = true) from by simp)]
      rw [show SerParse.fracPart ⟨false, [0], frac, ex⟩
          = if frac = [] then [] else dot :: digitsOf frac from rfl,
        show SerParse.expPart ⟨false, [0], frac, ex⟩ = (ex.map SExp.bytes).getD [] from rfl,
        ← heq]
      rfl
    · intro hki
      constructor
      · by_contra hf
        exact absurd (hunk (Or.inl hf)) (by rw [hki]; simp)
      · by_contra hf
        exact absurd (hunk (Or.inr hf)) (by rw [hki]; simp)
    · intro k hk
      have := hcap0 k hk
      simp only [List.length_cons, List.length_nil]
      omega
  · obtain ⟨hrecb, hb1, hb9, hbd⟩ := digitNz_recover hnz
    obtain ⟨sI, -⟩ := nstepE (s := s0) (s' := St.NINT) (c := c) (o := 0) (o' := 1) (n := n)
      (by rcases hs0 with rfl | rfl <;> decide) (by decide) (by rw [← hst]; exact hst1) hdE
      (fun _ k hk => hcap0 k hk) (by simp)
    rw [sI] at hs1
    rw [← Option.some.inj hs1] at hrest
    obtain ⟨ds, L1, hds, heq1, hnd1, hrun1, hcaps⟩ :=
      nint_digits_inv N L (by omega) (by simp only [ofsMax]; omega)
        (fun k hk _ => hcap0 k hk) hrest hend
    obtain ⟨frac, ex, rest, hfr, hexwf, hunk, hnn, heq⟩ :=
      num_tail_inv N L1 (by
        have : L1.length ≤ L.length := by rw [heq1]; simp
        omega) (Or.inr rfl) (by omega) hnd1 hrun1 hend
    refine ⟨⟨false, (b - digit0) :: ds, frac, ex⟩, rest, rfl,
      ⟨Or.inr ⟨b - digit0, ds, rfl, hb1, hb9, hds⟩, hfr, hexwf⟩, ?_, ?_, ?_, hnn⟩
    · rw [SerParse.snum_bytes_append]
      simp only [if_neg (show ¬ (false = true) from by simp)]
      rw [show SerParse.fracPart ⟨false, (b - digit0) :: ds, frac, ex⟩
          = if frac = [] then [] else dot :: digitsOf frac from rfl,
        show SerParse.expPart ⟨false, (b - digit0) :: ds, frac, ex⟩
          = (ex.map SExp.bytes).getD [] from rfl,
        ← heq, digitsOf_cons, hrecb, List.cons_append, ← heq1, List.nil_append]
    · intro hki
      constructor
      · by_contra hf
        exact absurd (hunk (Or.inl hf)) (by rw [hki]; simp)
      · by_contra hf
        exact absurd (hunk (Or.inr hf)) (by rw [hki]; simp)
    · intro k hk
      have h1 := hcaps k hk (hkc k hk)
      simp only [List.length_cons]
      omega

/-! ## Literals -/

theorem peel_fixed {s s' : St} {c : Option Claim} {o n : ℕ} {L : List ℕ} {rEnd : Regs} {bb : ℕ}
    (hne : s ≠ St.END) (hns : inStr s = false)
    (hval : Step.inValP s = true) (ho : o ≤ ofsMax - 1)
    (hstEq : ∀ (kind : Kind) (sp : Bool) (b : ℕ),
      stepSt kind sp s b = (if (b == bb) = true then some s' else none))
    (hnd : dEmit s bb = false)
    (hmi : (decide (s = St.PVAL) && (bb == minus)) = false)
    (htr : (decide (s = St.T3) && (bb == lowerE)) = false)
    (hs'k : s' ≠ St.KEY)
    (h : runL (nRegs s c o n) L = some rEnd) (hend : rEnd.st = St.END) :
    ∃ L', L = bb :: L' ∧ runL (nRegs s' c o n) L' = some rEnd := by
  obtain ⟨b, L', r1, rfl, hs1, hrest⟩ := peel_num hne h hend
  have hst1 := (Step.step_fields hs1).2.1
  rw [show (nRegs s c o n).st = s from rfl, show (nRegs s c o n).claim = c from rfl,
    show decide ((nRegs s c o n).sub = Sub.PLAIN) = true from rfl, hstEq] at hst1
  split_ifs at hst1 with hb
  · have hbb : b = bb := by simpa using hb
    subst hbb
    obtain ⟨sq, -⟩ := nstepQ (s := s) (s' := s') (c := c) (o := o) (o' := o) (n := n)
      hns hs'k (by rw [hstEq, if_pos hb]) hnd hmi htr
      (by rw [if_pos hval]; exact Nat.min_eq_left ho)
    rw [sq] at hs1
    rw [← Option.some.inj hs1] at hrest
    exact ⟨L', rfl, hrest⟩

theorem true_inv {c : Option Claim} {n : ℕ} {L : List ℕ} {rEnd : Regs}
    (h : runL (nRegs St.T1 c 0 n) L = some rEnd) (hend : rEnd.st = St.END) :
    ∃ rest, L = lowerR :: lowerU :: lowerE :: rest ∧
      runL (nRegs St.AVAL c 0 n) rest = some rEnd := by
  obtain ⟨L1, rfl, h1⟩ := peel_fixed (s := St.T1) (s' := St.T2) (bb := lowerR) (by decide)
    (by decide) (by decide) (by simp only [ofsMax]; omega) (fun _ _ _ => stepSt_t1_eq _ _ _)
    (by decide) (by decide) (by decide) (by decide) h hend
  obtain ⟨L2, rfl, h2⟩ := peel_fixed (s := St.T2) (s' := St.T3) (bb := lowerU) (by decide)
    (by decide) (by decide) (by simp only [ofsMax]; omega) (fun _ _ _ => stepSt_t2_eq _ _ _)
    (by decide) (by decide) (by decide) (by decide) h1 hend
  obtain ⟨b3, L3, r3, rfl, hs3, hrest3⟩ := peel_num (s := St.T3) (by decide) h2 hend
  have hst3 := (Step.step_fields hs3).2.1
  rw [show (nRegs St.T3 c 0 n).st = St.T3 from rfl,
    show (nRegs St.T3 c 0 n).claim = c from rfl,
    show decide ((nRegs St.T3 c 0 n).sub = Sub.PLAIN) = true from rfl, stepSt_t3_eq] at hst3
  split_ifs at hst3 with hb3
  · have hbb : b3 = lowerE := by simpa using hb3
    subst hbb
    obtain ⟨sq, -⟩ := nstepT (c := c) (o := 0) (n := n) (by simp only [ofsMax]; omega)
    rw [sq] at hs3
    rw [← Option.some.inj hs3] at hrest3
    exact ⟨L3, rfl, hrest3⟩

theorem false_inv {c : Option Claim} {n : ℕ} {L : List ℕ} {rEnd : Regs}
    (h : runL (nRegs St.F1 c 0 n) L = some rEnd) (hend : rEnd.st = St.END) :
    ∃ rest, L = lowerA :: 0x6C :: 0x73 :: lowerE :: rest ∧
      runL (nRegs St.AVAL c 0 n) rest = some rEnd := by
  obtain ⟨L1, rfl, h1⟩ := peel_fixed (s := St.F1) (s' := St.F2) (bb := lowerA) (by decide)
    (by decide) (by decide) (by simp only [ofsMax]; omega) (fun _ _ _ => stepSt_f1_eq _ _ _)
    (by decide) (by decide) (by decide) (by decide) h hend
  obtain ⟨L2, rfl, h2⟩ := peel_fixed (s := St.F2) (s' := St.F3) (bb := 0x6C) (by decide)
    (by decide) (by decide) (by simp only [ofsMax]; omega) (fun _ _ _ => stepSt_f2_eq _ _ _)
    (by decide) (by decide) (by decide) (by decide) h1 hend
  obtain ⟨L3, rfl, h3⟩ := peel_fixed (s := St.F3) (s' := St.F4) (bb := 0x73) (by decide)
    (by decide) (by decide) (by simp only [ofsMax]; omega) (fun _ _ _ => stepSt_f3_eq _ _ _)
    (by decide) (by decide) (by decide) (by decide) h2 hend
  obtain ⟨L4, rfl, h4⟩ := peel_fixed (s := St.F4) (s' := St.AVAL) (bb := lowerE) (by decide)
    (by decide) (by decide) (by simp only [ofsMax]; omega) (fun _ _ _ => stepSt_f4_eq _ _ _)
    (by decide) (by decide) (by decide) (by decide) h3 hend
  exact ⟨L4, rfl, h4⟩

theorem null_inv {c : Option Claim} {n : ℕ} {L : List ℕ} {rEnd : Regs}
    (h : runL (nRegs St.N1 c 0 n) L = some rEnd) (hend : rEnd.st = St.END) :
    ∃ rest, L = lowerU :: 0x6C :: 0x6C :: rest ∧
      runL (nRegs St.AVAL c 0 n) rest = some rEnd := by
  obtain ⟨L1, rfl, h1⟩ := peel_fixed (s := St.N1) (s' := St.N2) (bb := lowerU) (by decide)
    (by decide) (by decide) (by simp only [ofsMax]; omega) (fun _ _ _ => stepSt_n1_eq _ _ _)
    (by decide) (by decide) (by decide) (by decide) h hend
  obtain ⟨L2, rfl, h2⟩ := peel_fixed (s := St.N2) (s' := St.N3) (bb := 0x6C) (by decide)
    (by decide) (by decide) (by simp only [ofsMax]; omega) (fun _ _ _ => stepSt_n2_eq _ _ _)
    (by decide) (by decide) (by decide) (by decide) h1 hend
  obtain ⟨L3, rfl, h3⟩ := peel_fixed (s := St.N3) (s' := St.AVAL) (bb := 0x6C) (by decide)
    (by decide) (by decide) (by simp only [ofsMax]; omega) (fun _ _ _ => stepSt_n3_eq _ _ _)
    (by decide) (by decide) (by decide) (by decide) h2 hend
  exact ⟨L3, rfl, h3⟩

/-! ## A whole value -/

theorem kind_some_ne_unk : ∀ k : Claim, kindOf (some k) ≠ Kind.unk := by decide
theorem isStr_of_kind : ∀ k : Claim, kindOf (some k) = Kind.str → isStrClaim k = true := by decide
theorem isInt_of_kind : ∀ k : Claim, kindOf (some k) = Kind.int →
    isStrClaim k = false ∧ isIntClaim k = true := by decide
theorem isBool_of_kind : ∀ k : Claim, kindOf (some k) = Kind.bool →
    isStrClaim k = false ∧ isIntClaim k = false := by decide

theorem numOk {c : Option Claim} {nm : SNum} (hk : kindOf c = Kind.int ∨ kindOf c = Kind.unk)
    (hfe : kindOf c = Kind.int → nm.frac = [] ∧ nm.exp = none)
    (hcap : ∀ k : Claim, c = some k → nm.ints.length ≤ claimCap k) : SV.Ok c (SV.num nm) := by
  cases hc : c with
  | none => trivial
  | some k =>
    have hkint : kindOf (some k) = Kind.int := by
      rw [hc] at hk
      rcases hk with hh | hh
      · exact hh
      · exact absurd hh (kind_some_ne_unk k)
    obtain ⟨hns, hni⟩ := isInt_of_kind k hkint
    show (if isStrClaim k = true then _ else if isIntClaim k = true then
        ∃ nm', SV.num nm = .num nm' ∧ nm'.frac = [] ∧ nm'.exp = none ∧
          nm'.ints.length ≤ claimCap k
      else _)
    rw [if_neg (by simp [hns]), if_pos hni]
    obtain ⟨hf, he⟩ := hfe (by rw [hc]; exact hkint)
    exact ⟨nm, rfl, hf, he, hcap k hc⟩

theorem boolOk {c : Option Claim} {v : SV} (hk : kindOf c = Kind.bool ∨ kindOf c = Kind.unk)
    (hv : v = SV.btrue ∨ v = SV.bfalse) : SV.Ok c v := by
  cases hc : c with
  | none => trivial
  | some k =>
    have hkb : kindOf (some k) = Kind.bool := by
      rw [hc] at hk
      rcases hk with hh | hh
      · exact hh
      · exact absurd hh (kind_some_ne_unk k)
    obtain ⟨hns, hni⟩ := isBool_of_kind k hkb
    show (if isStrClaim k = true then _ else if isIntClaim k = true then _ else
      v = SV.btrue ∨ v = SV.bfalse)
    rw [if_neg (by simp [hns]), if_neg (by simp [hni])]
    exact hv

set_option maxHeartbeats 2000000 in
theorem value_inv : ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {c : Option Claim} {n : ℕ} {rEnd : Regs},
    NotWsHead L → runL (nRegs St.PVAL c 0 n) L = some rEnd → rEnd.st = St.END →
    ∃ (v : SV) (rest : List ℕ), v.WF ∧ SV.Ok c v ∧ L = v.bytes ++ rest ∧ NotNumHead rest := by
  intro N L hL c n rEnd hnws h hend
  obtain ⟨b, L', r1, rfl, hs1, hrest⟩ := peel_num (s := St.PVAL) (by decide) h hend
  have hst1 := (Step.step_fields hs1).2.1
  rw [show (nRegs St.PVAL c 0 n).st = St.PVAL from rfl,
    show (nRegs St.PVAL c 0 n).claim = c from rfl,
    show decide ((nRegs St.PVAL c 0 n).sub = Sub.PLAIN) = true from rfl] at hst1
  have hbnws : Model.isWs b = false := hnws b L' rfl
  simp only [List.length_cons] at hL
  rw [stepSt_pval_eq, if_neg (by simp [hbnws])] at hst1
  split_ifs at hst1 with c2 c3 c4 c5 c6 c7 c8
  · -- a string value
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at c2
    obtain ⟨hbq, hk⟩ := c2
    subst hbq
    obtain ⟨sS, -⟩ := nstepQ (s := St.PVAL) (s' := St.STR) (b := quote) (c := c) (o := 0)
      (o' := 0) (n := n) (by decide) (by decide) (stepSt_pval_quote hk) (by decide) (by decide)
      (by decide) (by simp)
    rw [sS] at hs1
    rw [← Option.some.inj hs1] at hrest
    have hstr : runL (sRegs Sub.PLAIN 0 c 0 n) L' = some rEnd := hrest
    obtain ⟨body, rest, heq, hwf⟩ := strBody_shape N L' (by omega)
      (show inStr (sRegs Sub.PLAIN 0 c 0 n).st = true from rfl) rfl hstr hend
    have hcaps : (kindOf c = Kind.str ∨ kindOf c = Kind.int) →
        (∀ e ∈ body, e.mcp < 0x80) ∧ (∀ k : Claim, c = some k → body.length ≤ claimCap k) := by
      intro hki
      rw [heq, RunList.runL_append] at hstr
      cases hx : runL (sRegs Sub.PLAIN 0 c 0 n) (seBytes body) with
      | none => rw [hx] at hstr; simp at hstr
      | some r2 =>
        obtain ⟨ha, hb'⟩ := strBody_caps body hwf hki (by simp only [ofsMax]; omega)
          (by intro k _; omega) hx
        exact ⟨ha, by intro k hk'; have := hb' k hk'; omega⟩
    have hbrun := (str_body_run body hwf c 0 n (by simp only [ofsMax]; omega)
      (fun hki k hk => by have := (hcaps hki).2 k hk; omega) (fun hki => (hcaps hki).1)).1
    have hstr2 : runL (sRegs Sub.PLAIN 0 c 0 n) L' = some rEnd := hstr
    rw [heq, RunList.runL_append_of hbrun] at hstr2
    obtain ⟨hclq, -⟩ := step_closeStr (c := c)
      (o := min (0 + body.length) (ofsMax - 1)) (n := n) (by omega)
    obtain ⟨rq, hsq, hrq⟩ := runL_cons_inv hstr2
    rw [hclq] at hsq
    rw [← Option.some.inj hsq] at hrq
    refine ⟨SV.str body, rest, hwf, ?_, ?_, notNumHead_aval rfl hrq⟩
    · cases hc : c with
      | none => trivial
      | some k =>
        have hkstr : kindOf (some k) = Kind.str := by
          rw [hc] at hk
          rcases hk with hh | hh
          · exact hh
          · exact absurd hh (kind_some_ne_unk k)
        have hstrk : isStrClaim k = true := isStr_of_kind k hkstr
        show (if isStrClaim k = true then
            ∃ bd, SV.str body = .str bd ∧ (∀ e ∈ bd, e.mcp < 0x80) ∧ bd.length ≤ claimCap k
          else _)
        rw [if_pos hstrk]
        refine ⟨body, rfl, ?_, ?_⟩
        · exact (hcaps (by rw [hc]; exact Or.inl hkstr)).1
        · exact (hcaps (by rw [hc]; exact Or.inl hkstr)).2 k hc
    · rw [heq]
      simp [SV.bytes, List.append_assoc]
  · -- a negative number
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at c3
    obtain ⟨hbm, hk⟩ := c3
    subst hbm
    obtain ⟨sN, -⟩ := nstepM (c := c) (o := 0) (n := n) (stepSt_pval_minus hk true)
    rw [sN] at hs1
    rw [← Option.some.inj hs1] at hrest
    obtain ⟨b2, L2, r2, rfl, hs2, hrest2⟩ := peel_num (s := St.NSIGN) (by decide) hrest hend
    have hst2 := (Step.step_fields hs2).2.1
    rw [show (nRegs St.NSIGN c 0 n).st = St.NSIGN from rfl,
      show (nRegs St.NSIGN c 0 n).claim = c from rfl,
      show decide ((nRegs St.NSIGN c 0 n).sub = Sub.PLAIN) = true from rfl] at hst2
    have hdb : Model.isDigit b2 = true := by
      rcases stepSt_nsign_num_inv hst2 with ⟨hb2, -⟩ | ⟨hb2, -⟩
      · rw [hb2]; decide
      · exact (digitNz_recover hb2).2.2.2
    obtain ⟨nm, rest, hneg, hwfn, heqn, hfe, hcapn, hnnr⟩ :=
      num_inv N L2 (by simp only [List.length_cons] at hL; omega) (Or.inr rfl) hk hdb hrest hend
    refine ⟨SV.num ⟨true, nm.ints, nm.frac, nm.exp⟩, rest, hwfn, ?_, ?_, hnnr⟩
    · cases hc : c with
      | none => trivial
      | some k =>
        have hkint : kindOf (some k) = Kind.int := by
          rw [hc] at hk
          rcases hk with hh | hh
          · exact hh
          · exact absurd hh (kind_some_ne_unk k)
        obtain ⟨hns, hni⟩ := isInt_of_kind k hkint
        show (if isStrClaim k = true then _ else if isIntClaim k = true then
            ∃ nm', SV.num ⟨true, nm.ints, nm.frac, nm.exp⟩ = .num nm' ∧ nm'.frac = [] ∧
              nm'.exp = none ∧ nm'.ints.length ≤ claimCap k
          else _)
        rw [if_neg (by simp [hns]), if_pos hni]
        obtain ⟨hf, he⟩ := hfe (by rw [hc]; exact hkint)
        exact ⟨⟨true, nm.ints, nm.frac, nm.exp⟩, rfl, hf, he, hcapn k hc⟩
    · have hbeq : SV.bytes (SV.num ⟨true, nm.ints, nm.frac, nm.exp⟩) = minus :: nm.bytes := by
        show SNum.bytes ⟨true, nm.ints, nm.frac, nm.exp⟩ = minus :: SNum.bytes nm
        simp [SNum.bytes, hneg]
      rw [hbeq, List.cons_append, ← heqn]
  · -- zero
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at c4
    obtain ⟨hb0, hk⟩ := c4
    obtain ⟨nm, rest, hneg, hwfn, heqn, hfe, hcapn, hnnr⟩ :=
      num_inv N L' (by omega) (Or.inl rfl) hk (by rw [hb0]; decide) h hend
    exact ⟨SV.num nm, rest, hwfn, numOk hk hfe hcapn, heqn, hnnr⟩
  · -- a nonzero number
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at c5
    obtain ⟨hnz, hk⟩ := c5
    obtain ⟨nm, rest, hneg, hwfn, heqn, hfe, hcapn, hnnr⟩ :=
      num_inv N L' (by omega) (Or.inl rfl) hk (digitNz_recover hnz).2.2.2 h hend
    exact ⟨SV.num nm, rest, hwfn, numOk hk hfe hcapn, heqn, hnnr⟩
  · -- true
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at c6
    obtain ⟨hbt, hk⟩ := c6
    subst hbt
    obtain ⟨sT, -⟩ := nstepQ (s := St.PVAL) (s' := St.T1) (b := lowerT) (c := c) (o := 0)
      (o' := 0) (n := n) (by decide) (by decide) (stepSt_pval_t hk true) (by decide) (by decide)
      (by decide) (by simp)
    rw [sT] at hs1
    rw [← Option.some.inj hs1] at hrest
    obtain ⟨rest, hrq, hrun'⟩ := true_inv hrest hend
    exact ⟨SV.btrue, rest, trivial, boolOk hk (Or.inl rfl), by rw [hrq]; rfl,
      notNumHead_aval rfl hrun'⟩
  · -- false
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at c7
    obtain ⟨hbf, hk⟩ := c7
    subst hbf
    obtain ⟨sF, -⟩ := nstepQ (s := St.PVAL) (s' := St.F1) (b := lowerF) (c := c) (o := 0)
      (o' := 0) (n := n) (by decide) (by decide) (stepSt_pval_f hk true) (by decide) (by decide)
      (by decide) (by simp)
    rw [sF] at hs1
    rw [← Option.some.inj hs1] at hrest
    obtain ⟨rest, hrq, hrun'⟩ := false_inv hrest hend
    exact ⟨SV.bfalse, rest, trivial, boolOk hk (Or.inr rfl), by rw [hrq]; rfl,
      notNumHead_aval rfl hrun'⟩
  · -- null
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c8
    obtain ⟨hbn, hk⟩ := c8
    subst hbn
    obtain ⟨sNl, -⟩ := nstepQ (s := St.PVAL) (s' := St.N1) (b := lowerN) (c := c) (o := 0)
      (o' := 0) (n := n) (by decide) (by decide) (stepSt_pval_n hk true) (by decide) (by decide)
      (by decide) (by simp)
    rw [sNl] at hs1
    rw [← Option.some.inj hs1] at hrest
    obtain ⟨rest, hrq, hrun'⟩ := null_inv hrest hend
    refine ⟨SV.null, rest, trivial, ?_, by rw [hrq]; rfl, notNumHead_aval rfl hrun'⟩
    cases hc : c with
    | none => trivial
    | some k => exact absurd (by rw [← hc]; exact hk) (kind_some_ne_unk k)

/-! ## A whole member -/

theorem claim_of_key (key : List SE) :
    ((List.finRange nClaims).find? fun k : Claim =>
      ((Vector.ofFn fun k' : Claim =>
          mAfter k' ((Vector.ofFn fun _ : Claim => true)[k']) 0 (mcps key))[k]
        && decide (kIdxAfter 0 key.length = (claimName k).length)))
      = (List.finRange nClaims).find? (fun k : Claim => decide (mcps key = claimName k)) := by
  congr 1
  funext k
  simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  have hml : key.length = (mcps key).length := (mcps_length key).symm
  simp only [hml]
  exact match_flag (mcps key) k

set_option maxHeartbeats 2000000 in
theorem member_inv : ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {s : St}, (s = St.OBJ ∨ s = St.SEP) →
    ∀ {c0 : Option Claim} {n : ℕ} {r rEnd : Regs}, AtS s c0 n r →
    (∀ w L1, L = w ++ L1 → IsWs w → NotWsHead L1 → ∃ t, L1 = quote :: t) →
    runL r L = some rEnd → rEnd.st = St.END →
    ∃ (m : SMem) (rest : List ℕ) (r' : Regs), m.WF ∧ L = m.bytes ++ rest ∧
      AtE m.claim (n + 1) r' ∧ runL r' rest = some rEnd ∧ NotWsHead rest ∧
      NotNumHead rest := by
  intro N L hL s hs c0 n r rEnd hr hquote h hend
  -- the leading whitespace
  obtain ⟨ws0, L1, r1, hL1, hws0, hnw1, hrun1, ha1⟩ := ws_peel (by rcases hs with rfl | rfl <;> decide) hr L h
  obtain ⟨L2, hL2⟩ := hquote ws0 L1 hL1 hws0 hnw1
  subst hL2
  -- the opening quote
  obtain ⟨r2, hs2, hrun2⟩ := runL_cons_inv hrun1
  obtain ⟨sq, -⟩ := step_openQuote hs ha1
  rw [sq] at hs2
  rw [← Option.some.inj hs2] at hrun2
  -- the key body
  obtain ⟨key, L3, hL3, hkeywf⟩ := strBody_shape N L2
    (by subst hL1; simp only [List.length_append, List.length_cons] at hL; omega)
    (show inStr (kRegs Sub.PLAIN 0 0 (Vector.ofFn fun _ : Claim => true) (n + 1)).st = true
      from rfl) rfl hrun2 hend
  subst hL3
  obtain ⟨hbody, -⟩ := key_body_run key hkeywf 0 (n + 1) (by simp only [kIdxMax]; omega)
    (Vector.ofFn fun _ : Claim => true)
  rw [RunList.runL_append_of hbody] at hrun2
  -- the closing quote
  obtain ⟨r4, hs4, ha4, -, -, -, -⟩ := step_closeKey
    (i := kIdxAfter 0 key.length)
    (mv := Vector.ofFn fun k' : Claim => mAfter k' ((Vector.ofFn fun _ : Claim => true)[k']) 0
      (mcps key)) (n := n + 1)
  obtain ⟨r4', hs4', hrun4⟩ := runL_cons_inv hrun2
  rw [hs4] at hs4'
  rw [← Option.some.inj hs4'] at hrun4
  rw [claim_of_key key] at ha4
  set cl : Option Claim :=
    (List.finRange nClaims).find? (fun k : Claim => decide (mcps key = claimName k)) with hcl
  -- the whitespace before the colon
  obtain ⟨ws1, L4, r5, hL4, hws1, hnw4, hrun5, ha5⟩ := ws_peel (by decide) ha4 L3 hrun4
  subst hL4
  -- the colon
  have hne5 : L4 ≠ [] := by
    intro hnil
    subst hnil
    rw [RunList.runL_nil, Option.some.injEq] at hrun5
    rw [← hrun5, ha5.1] at hend
    exact absurd hend (by decide)
  obtain ⟨b5, L5, hL5⟩ : ∃ b5 L5, L4 = b5 :: L5 := by
    cases L4 with
    | nil => exact absurd rfl hne5
    | cons a t => exact ⟨a, t, rfl⟩
  subst hL5
  obtain ⟨r6, hs6, hrun6⟩ := runL_cons_inv hrun5
  have hst6 := (Step.step_fields hs6).2.1
  rw [ha5.1, ha5.2.2.1, ha5.2.1] at hst6
  simp only [decide_true] at hst6
  rw [stepSt_akey_eq, if_neg (by simp [hnw4 b5 L5 rfl])] at hst6
  have hb5 : b5 = colon := by
    split_ifs at hst6 with hb
    · simpa using hb
  subst hb5
  have hcolon : step r5 colon = some (normal St.PVAL cl (n + 1)) :=
    step_struct ha5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (stepSt_akey_colon _ _)
  rw [hcolon] at hs6
  rw [← Option.some.inj hs6] at hrun6
  -- the whitespace before the value
  obtain ⟨ws2, L6, hL6, hws2, hnw6, hrun7⟩ := ws_peel_normal (s := St.PVAL) (c := cl)
    (n := n + 1) (by decide) L5 hrun6
  subst hL6
  -- the value
  have hlen6 : L6.length ≤ N := by
    subst hL1
    simp only [List.length_append, List.length_cons] at hL
    omega
  obtain ⟨v, L7, hvwf, hvok, hL7, hnn7⟩ := value_inv N L6 hlen6 hnw6
    (show runL (nRegs St.PVAL cl 0 (n + 1)) L6 = some rEnd from hrun7) hend
  subst hL7
  obtain ⟨rv, hvrun, hvate, -⟩ := value_run (v := v) hvwf (c := cl) (n := n + 1) hvok
  rw [show normal St.PVAL cl (n + 1) = nRegs St.PVAL cl 0 (n + 1) from rfl,
    RunList.runL_append_of hvrun] at hrun7
  -- the trailing whitespace
  obtain ⟨ws3, rest, r8, hL8, hws3, hnwr, hrun8, ha8, hnil8, hav8⟩ := ws_peel_AtE L7 hvate hrun7
  have hnnrest : NotNumHead rest := by
    by_cases hwn : ws3 = []
    · subst hwn
      rw [List.nil_append] at hL8
      rw [← hL8]
      exact hnn7
    · exact notNumHead_aval (hav8 hwn) hrun8
  subst hL8
  refine ⟨⟨ws0, key, ws1, ws2, v, ws3⟩, rest, r8, ⟨hws0, hws1, hws2, hws3, hkeywf, hvwf, ?_⟩,
    ?_, ?_, hrun8, hnwr, hnnrest⟩
  · show SV.Ok (SMem.claim ⟨ws0, key, ws1, ws2, v, ws3⟩) v
    rw [show SMem.claim ⟨ws0, key, ws1, ws2, v, ws3⟩ = cl from rfl]
    exact hvok
  · rw [hL1, SMem.bytes]
    simp [List.append_assoc]
  · rw [show SMem.claim ⟨ws0, key, ws1, ws2, v, ws3⟩ = cl from rfl]
    exact ha8

/-! ## The list of members -/

theorem ws_split_eq : ∀ (w L' L : List ℕ), L = w ++ L' → IsWs w → NotWsHead L' →
    L' = L.dropWhile Model.isWs := by
  intro w
  induction w with
  | nil =>
    intro L' L hL _ hn
    subst hL
    cases hx : L with
    | nil => rfl
    | cons c t =>
      rw [List.dropWhile_cons, if_neg (by simp [hn c t hx])]
  | cons b w ih =>
    intro L' L hL hw hn
    subst hL
    have hb : Model.isWs b = true := hw b (List.mem_cons_self ..)
    rw [List.cons_append, List.dropWhile_cons, if_pos (by simp [hb])]
    exact ih L' (w ++ L') rfl (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hn

theorem ws_split_unique {L w1 L1 w2 L2 : List ℕ} (h1 : L = w1 ++ L1) (hw1 : IsWs w1)
    (hn1 : NotWsHead L1) (h2 : L = w2 ++ L2) (hw2 : IsWs w2) (hn2 : NotWsHead L2) : L1 = L2 := by
  rw [ws_split_eq w1 L1 L h1 hw1 hn1, ws_split_eq w2 L2 L h2 hw2 hn2]

theorem end_inv : ∀ (L : List ℕ) {c : Option Claim} {n : ℕ} {r rEnd : Regs},
    AtS St.END c n r → runL r L = some rEnd → IsWs L := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _; intro x hx; simp at hx
  | cons b L ih =>
    intro c n r rEnd hr h
    obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
    have hst1 := (Step.step_fields hs1).2.1
    rw [hr.1, hr.2.2.1, hr.2.1] at hst1
    simp only [decide_true] at hst1
    rw [stepSt_end_eq] at hst1
    have hb : Model.isWs b = true := by
      split_ifs at hst1 with hx
      · exact hx
    have hstep : step r b = some (normal St.END c n) := by
      have := step_ws (r := r) hb (by rw [hr.1]; decide) hr.2.1
      rwa [hr.1, hr.2.2.1, hr.2.2.2] at this
    rw [hstep] at hs1
    rw [← Option.some.inj hs1] at hrest
    have := ih (atS_normal St.END c n) hrest
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb
    · exact this x hx

theorem smem_bytes_ne_nil (m : SMem) : SMem.bytes m ≠ [] := by
  intro he
  have : (SMem.bytes m).length = 0 := by rw [he]; rfl
  rw [SMem.bytes] at this
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

/-- At `SEP` the next non-whitespace byte is the opening quote of a member. -/
theorem sep_quote {c : Option Claim} {n : ℕ} {r rEnd : Regs} {L : List ℕ}
    (hr : AtS St.SEP c n r) (h : runL r L = some rEnd) (hend : rEnd.st = St.END) :
    ∀ w L1, L = w ++ L1 → IsWs w → NotWsHead L1 → ∃ t, L1 = quote :: t := by
  obtain ⟨w0, L0, r0, hL0, hw0, hn0, hrun0, ha0⟩ := ws_peel (by decide) hr L h
  have hne : L0 ≠ [] := by
    intro hnil
    subst hnil
    rw [RunList.runL_nil, Option.some.injEq] at hrun0
    rw [← hrun0, ha0.1] at hend
    exact absurd hend (by decide)
  obtain ⟨b, t, hbt⟩ : ∃ b t, L0 = b :: t := by
    cases L0 with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  subst hbt
  obtain ⟨r1, hs1, -⟩ := runL_cons_inv hrun0
  have hst1 := (Step.step_fields hs1).2.1
  rw [ha0.1, ha0.2.2.1, ha0.2.1] at hst1
  simp only [decide_true] at hst1
  rw [stepSt_sep_eq, if_neg (by simp [hn0 b t rfl])] at hst1
  have hbq : b = quote := by
    split_ifs at hst1 with hx
    · simpa using hx
  subst hbq
  intro w L1 hL1 hw hn
  exact ⟨t, ws_split_unique hL1 hw hn hL0 hw0 hn0⟩

set_option maxHeartbeats 2000000 in
theorem members_inv : ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {c : Option Claim} {n : ℕ} {r rEnd : Regs}, AtE c n r → NotWsHead L → NotNumHead L →
    runL r L = some rEnd → rEnd.st = St.END →
    ∃ (ms : List SMem) (post : List ℕ), (∀ m ∈ ms, m.WF) ∧ IsWs post ∧
      L = (ms.map fun m' => comma :: SMem.bytes m').flatten ++ (rbrace :: post) := by
  intro N
  induction N with
  | zero =>
    intro L hL c n r rEnd hr hnw hnn h hend
    exfalso
    have hnil : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    rw [RunList.runL_nil, Option.some.injEq] at h
    rw [← h] at hend
    have hx := hr.1
    rw [hend] at hx
    exact absurd hx (by decide)
  | succ N ih =>
    intro L hL c n r rEnd hr hnw hnn h hend
    cases L with
    | nil =>
      exfalso
      rw [RunList.runL_nil, Option.some.injEq] at h
      rw [← h] at hend
      have hx := hr.1
      rw [hend] at hx
      exact absurd hx (by decide)
    | cons b L' =>
      simp only [List.length_cons] at hL
      obtain ⟨r1, hs1, hrest⟩ := runL_cons_inv h
      obtain ⟨hbd, hbdot, hbexp⟩ := hnn b L' rfl
      have hst1 := (Step.step_fields hs1).2.1
      rw [hr.2.2.1, hr.2.1] at hst1
      simp only [decide_true] at hst1
      rw [stepSt_endVal _ _ _ _ hr.1 hbd (by simp [hbdot]) hbexp] at hst1
      have hbw : Model.isWs b = false := hnw b L' rfl
      rw [afterValue, if_neg (by simp [hbw])] at hst1
      by_cases hbc : (b == comma) = true
      · have hbc' : b = comma := by simpa using hbc
        subst hbc'
        obtain ⟨r2, hs2, ha2, -⟩ := step_endVal_comma hr
        rw [hs2] at hs1
        rw [← Option.some.inj hs1] at hrest
        obtain ⟨m, rest, r3, hmwf, hL3, ha3, hrun3, hnw3, hnn3⟩ :=
          member_inv N L' (by omega) (Or.inr rfl) ha2 (sep_quote ha2 hrest hend) hrest hend
        have hlt : rest.length < L'.length := by
          rw [hL3, List.length_append]
          have : 1 ≤ (SMem.bytes m).length := by
            cases hx : SMem.bytes m with
            | nil => exact absurd hx (smem_bytes_ne_nil m)
            | cons a t => simp
          omega
        obtain ⟨ms, post, hmswf, hpost, hrq⟩ :=
          ih rest (by omega) ha3 hnw3 hnn3 hrun3 hend
        refine ⟨m :: ms, post, ?_, hpost, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hmwf
          · exact hmswf x hx
        · rw [hL3, hrq]
          simp [List.append_assoc]
      · rw [if_neg (by simp [hbc])] at hst1
        by_cases hbr : (b == rbrace) = true
        · have hbr' : b = rbrace := by simpa using hbr
          subst hbr'
          obtain ⟨r2, hs2, ha2, -⟩ := step_endVal_rbrace hr
          rw [hs2] at hs1
          rw [← Option.some.inj hs1] at hrest
          exact ⟨[], L', by simp, end_inv L' ha2 hrest, by simp⟩
        · rw [if_neg (by simp [hbr])] at hst1
          exact absurd hst1 (by simp)

/-! ## The whole body and the whole serialization -/

set_option maxHeartbeats 1000000 in
theorem body_inv : ∀ (N : ℕ) (L : List ℕ), L.length ≤ N →
    ∀ {c0 : Option Claim} {n : ℕ} {r rEnd : Regs}, AtS St.OBJ c0 n r →
    runL r L = some rEnd → rEnd.st = St.END →
    ∃ (ms : List SMem) (we post : List ℕ), (∀ m ∈ ms, m.WF) ∧ IsWs we ∧ IsWs post ∧
      L = bodyBytes ms we ++ (rbrace :: post) := by
  intro N L hL c0 n r rEnd hr h hend
  obtain ⟨we, L1, r1, hL1, hwe, hn1, hrun1, ha1⟩ := ws_peel (by decide) hr L h
  have hne : L1 ≠ [] := by
    intro hnil
    subst hnil
    rw [RunList.runL_nil, Option.some.injEq] at hrun1
    rw [← hrun1, ha1.1] at hend
    exact absurd hend (by decide)
  obtain ⟨b, L2, hb2⟩ : ∃ b L2, L1 = b :: L2 := by
    cases L1 with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  subst hb2
  obtain ⟨r2, hs2, hrest⟩ := runL_cons_inv hrun1
  have hst2 := (Step.step_fields hs2).2.1
  rw [ha1.1, ha1.2.2.1, ha1.2.1] at hst2
  simp only [decide_true] at hst2
  rw [stepSt_obj_eq, if_neg (by simp [hn1 b L2 rfl])] at hst2
  by_cases hbq : (b == quote) = true
  · have hbq' : b = quote := by simpa using hbq
    subst hbq'
    obtain ⟨m, rest, r3, hmwf, hL3, ha3, hrun3, hnw3, hnn3⟩ :=
      member_inv N L hL (Or.inl rfl) hr
        (fun w L1' hLe hw hn => ⟨L2, ws_split_unique hLe hw hn hL1 hwe hn1⟩) h hend
    have hlt : rest.length ≤ N := by
      rw [hL3, List.length_append] at hL
      omega
    obtain ⟨ms, post, hmswf, hpost, hrq⟩ := members_inv N rest hlt ha3 hnw3 hnn3 hrun3 hend
    refine ⟨m :: ms, [], post, ?_, by intro x hx; simp at hx, hpost, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hmwf
      · exact hmswf x hx
    · rw [hL3, hrq, bodyBytes]
      simp [List.append_assoc]
  · rw [if_neg (by simp [hbq])] at hst2
    by_cases hbr : (b == rbrace) = true
    · have hbr' : b = rbrace := by simpa using hbr
      subst hbr'
      have hstep : step r1 rbrace = some (normal St.END c0 n) :=
        step_struct ha1 (by decide) (by decide) (by decide) (by decide) (by decide)
          (stepSt_obj_rbrace _ _)
      rw [hstep] at hs2
      rw [← Option.some.inj hs2] at hrest
      exact ⟨[], we, L2, by intro x hx; simp at hx, hwe,
        end_inv L2 (atS_normal St.END c0 n) hrest, by rw [hL1]; rfl⟩
    · rw [if_neg (by simp [hbr])] at hst2
      exact absurd hst2 (by simp)

/-- **The inversion.**  An accepting run is the byte string of a structurally
well-formed serialization. -/
theorem ser_inv (L : List ℕ) {rEnd : Regs} (h : runL Regs.init L = some rEnd)
    (hend : rEnd.st = St.END) : ∃ sr : Ser, sr.SWF ∧ L = sr.bytes := by
  rw [init_eq_normal] at h
  obtain ⟨pre, L1, r1, hL1, hpre, hn1, hrun1, ha1⟩ :=
    ws_peel (by decide) (atS_normal St.PRE none 0) L h
  have hne : L1 ≠ [] := by
    intro hnil
    subst hnil
    rw [RunList.runL_nil, Option.some.injEq] at hrun1
    rw [← hrun1, ha1.1] at hend
    exact absurd hend (by decide)
  obtain ⟨b, L2, hb2⟩ : ∃ b L2, L1 = b :: L2 := by
    cases L1 with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  subst hb2
  obtain ⟨r2, hs2, hrest⟩ := runL_cons_inv hrun1
  have hst2 := (Step.step_fields hs2).2.1
  rw [ha1.1, ha1.2.2.1, ha1.2.1] at hst2
  simp only [decide_true] at hst2
  rw [stepSt_pre_eq, if_neg (by simp [hn1 b L2 rfl])] at hst2
  have hbl : b = lbrace := by
    split_ifs at hst2 with hx
    · simpa using hx
  subst hbl
  have hstep : step r1 lbrace = some (normal St.OBJ none 0) :=
    step_struct ha1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (stepSt_pre_lbrace _ _)
  rw [hstep] at hs2
  rw [← Option.some.inj hs2] at hrest
  obtain ⟨ms, we, post, hmswf, hwe, hpost, hL2⟩ :=
    body_inv L2.length L2 le_rfl (atS_normal St.OBJ none 0) hrest hend
  refine ⟨⟨pre, ms, we, post⟩, ⟨hpre, hwe, hpost, hmswf⟩, ?_⟩
  rw [hL1, hL2, Ser.bytes]
  simp [List.append_assoc]

end RunInv

end Solution.JSONExtract
