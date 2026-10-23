import Solution.JSONExtract.RunTheory

/-!
# The automaton over a byte *list* (`JSONExtract`)

`Model.run` walks a byte *function* with a length cut-off, which is what the
circuit layer needs. For the grammar arguments a list is far more convenient:
`runL` is the same automaton over a `List ℕ`, `traceL` records the (state,
byte) pair of every position, and both compose over `++`. `run_toL` transports
`Model.run`, `Model.runSignals` and the four read-out counters of an accepting
run to the list level.
-/

namespace Solution.JSONExtract

open Model (St Sub Claim Regs)

namespace RunList

open Model

/-! ## The list-level automaton -/

/-- The automaton over a byte list: `none` as soon as a byte has no transition. -/
def runL : Regs → List ℕ → Option Regs
  | r, [] => some r
  | r, b :: L => (step r b).bind fun r' => runL r' L

/-- Every position of the run, as the state before the byte paired with the
byte. The list stops at the first rejected byte. -/
def traceL : Regs → List ℕ → List (Regs × ℕ)
  | _, [] => []
  | r, b :: L => (r, b) :: (match step r b with | some r' => traceL r' L | none => [])

@[simp] theorem runL_nil (r : Regs) : runL r [] = some r := rfl

@[simp] theorem runL_cons (r : Regs) (b : ℕ) (L : List ℕ) :
    runL r (b :: L) = (step r b).bind fun r' => runL r' L := rfl

@[simp] theorem traceL_nil (r : Regs) : traceL r [] = [] := rfl

theorem traceL_cons (r : Regs) (b : ℕ) (L : List ℕ) :
    traceL r (b :: L) = (r, b) :: (match step r b with | some r' => traceL r' L | none => []) :=
  rfl

@[simp] theorem traceL_cons_of_some {r r' : Regs} {b : ℕ} (h : step r b = some r') (L : List ℕ) :
    traceL r (b :: L) = (r, b) :: traceL r' L := by
  rw [traceL_cons, h]

@[simp] theorem runL_single (r : Regs) (b : ℕ) : runL r [b] = step r b := by
  simp [runL]

theorem traceL_single (r : Regs) (b : ℕ) : traceL r [b] = [(r, b)] := by
  rw [traceL_cons]; cases step r b <;> rfl

theorem runL_append (r : Regs) (L1 L2 : List ℕ) :
    runL r (L1 ++ L2) = (runL r L1).bind fun r' => runL r' L2 := by
  induction L1 generalizing r with
  | nil => simp
  | cons b L1 ih => simp only [List.cons_append, runL_cons, ih]; cases step r b <;> simp

theorem runL_append_of {r r1 : Regs} {L1 : List ℕ} (h : runL r L1 = some r1) (L2 : List ℕ) :
    runL r (L1 ++ L2) = runL r1 L2 := by rw [runL_append, h]; rfl

theorem traceL_append {r r1 : Regs} {L1 : List ℕ} (h : runL r L1 = some r1) (L2 : List ℕ) :
    traceL r (L1 ++ L2) = traceL r L1 ++ traceL r1 L2 := by
  induction L1 generalizing r with
  | nil => simp only [runL_nil, Option.some.injEq] at h; subst h; simp
  | cons b L1 ih =>
    rw [runL_cons] at h
    cases hs : step r b with
    | none => rw [hs] at h; simp at h
    | some r' =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      rw [List.cons_append, traceL_cons_of_some hs, traceL_cons_of_some hs, ih h, List.cons_append]

/-! ## Transport from `Model.run` -/

/-- The first `n` bytes, as a list. -/
def toL (bytes : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map bytes

@[simp] theorem toL_length (bytes : ℕ → ℕ) (n : ℕ) : (toL bytes n).length = n := by
  simp [toL]

theorem toL_succ (bytes : ℕ → ℕ) (n : ℕ) : toL bytes (n + 1) = toL bytes n ++ [bytes n] := by
  simp [toL, List.range_succ]

theorem toL_eq_ofFn (bytes : ℕ → ℕ) (n : ℕ) :
    toL bytes n = List.ofFn fun i : Fin n => bytes i := by
  apply List.ext_getElem <;> simp [toL]

section
variable {bytes : ℕ → ℕ} {len : ℕ}

theorem run_toL (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome) :
    ∀ n, n ≤ len →
      runL Regs.init (toL bytes n) = some (run bytes len n) ∧
        traceL Regs.init (toL bytes n)
          = (List.range n).map fun i => (run bytes len i, bytes i) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨ihr, iht⟩ := ih (by omega)
    obtain ⟨r', hs⟩ := Option.isSome_iff_exists.mp (hsteps n (by omega))
    have hnext : run bytes len (n + 1) = r' := RunTheory.run_succ_of_step (by omega) hs
    constructor
    · rw [toL_succ, runL_append_of ihr, runL_single, hs, hnext]
    · rw [toL_succ, traceL_append ihr, iht, traceL_single, List.range_succ, List.map_append]
      rfl

end

/-! ## The read-out predicates at the list level

Every field of `Model.signals` the read-outs look at is independent of the
successor state, so a `(state, byte)` pair determines it. -/

theorem sig_match_indep (r : Regs) (b : ℕ) (s s' : St) (k : Claim) :
    (signals r b s).match_[k] = (signals r b s').match_[k] := rfl

theorem sig_vEmit_indep (r : Regs) (b : ℕ) (s s' : St) :
    (signals r b s).vEmit = (signals r b s').vEmit := rfl

theorem sig_minus_indep (r : Regs) (b : ℕ) (s s' : St) :
    (signals r b s).minusFlag = (signals r b s').minusFlag := rfl

theorem sig_true_indep (r : Regs) (b : ℕ) (s s' : St) :
    (signals r b s).trueDone = (signals r b s').trueDone := rfl

theorem sig_valOut_indep (r : Regs) (b : ℕ) (s s' : St) :
    (signals r b s).valOut = (signals r b s').valOut := rfl

/-- Position `x` closes a key that matches claim `k`. -/
def pMatch (k : Claim) (x : Regs × ℕ) : Bool := (signals x.1 x.2 x.1.st).match_[k]
/-- Position `x` emits a value of claim `k`. -/
def pEmit (k : Claim) (x : Regs × ℕ) : Bool :=
  (signals x.1 x.2 x.1.st).vEmit && decide (x.1.claim = some k)
/-- Position `x` reads the `-` of claim `k`. -/
def pMinus (k : Claim) (x : Regs × ℕ) : Bool :=
  (signals x.1 x.2 x.1.st).minusFlag && decide (x.1.claim = some k)
/-- Position `x` finishes the literal `true` of claim `k`. -/
def pTrue (k : Claim) (x : Regs × ℕ) : Bool :=
  (signals x.1 x.2 x.1.st).trueDone && decide (x.1.claim = some k)
/-- The value position `x` routes. -/
def fVal (x : Regs × ℕ) : ℕ := (signals x.1 x.2 x.1.st).valOut

/-! ## Acceptance, unpacked -/

theorem accepts_iff (bytes : ℕ → ℕ) (len : ℕ) :
    accepts bytes len = true ↔
      ((∀ i, i < len → (step (run bytes len i) (bytes i)).isSome) ∧
        (run bytes len len).st = St.END ∧ (run bytes len len).sub = Sub.PLAIN ∧
        (run bytes len len).nMem ≤ Model.maxMembers ∧
        ∀ k : Claim, presentCount bytes len k ≤ 1) := by
  simp only [accepts, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun k => h5 k (List.mem_finRange k)⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun k _ => h5 k⟩

/-! ## Generic list facts -/

theorem range_split {i N : ℕ} (h : i < N) : ∃ l2, List.range N = List.range i ++ i :: l2 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_or_ge i N with hlt | hge
    · obtain ⟨l2, hl2⟩ := ih hlt
      exact ⟨l2 ++ [N], by rw [List.range_succ, hl2]; simp⟩
    · have : i = N := by omega
      subst this
      exact ⟨[], by rw [List.range_succ]⟩

theorem getD_filter_map {α : Type} (p : ℕ → Bool) (f : ℕ → α) (d : α)
    (l1 : List ℕ) (i : ℕ) (l2 : List ℕ) (hp : p i = true) :
    (((l1 ++ i :: l2).filter p).map f).getD (l1.filter p).length d = f i := by
  rw [List.filter_append, List.filter_cons, if_pos hp, List.map_append, List.map_cons]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem filter_map_length {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    ((l.map f).filter p).length = (l.filter fun a => p (f a)).length := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p (f a) <;> simp [h, ih]

theorem filter_map_map {α β γ : Type} (f : α → β) (p : β → Bool) (g : β → γ) (l : List α) :
    ((l.map f).filter p).map g = (l.filter fun a => p (f a)).map (fun a => g (f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p (f a) <;> simp [h, ih]

/-! ## The read-outs of an accepting run, at the list level -/

section
variable {bytes : ℕ → ℕ} {len : ℕ}

theorem runSignals_eq {i : ℕ} (hi : i < len) :
    runSignals bytes len i = signals (run bytes len i) (bytes i)
      ((step (run bytes len i) (bytes i)).getD (run bytes len i)).st := by
  simp only [runSignals, if_pos hi]

theorem pMatch_eq {i : ℕ} (hi : i < len) (k : Claim) :
    pMatch k (run bytes len i, bytes i) = (runSignals bytes len i).match_[k] := by
  rw [runSignals_eq hi]; rfl

theorem pEmit_eq {i : ℕ} (hi : i < len) (k : Claim) :
    pEmit k (run bytes len i, bytes i) = RunTheory.emitsAt bytes len k i := by
  rw [RunTheory.emitsAt, runSignals_eq hi]; rfl

theorem pMinus_eq {i : ℕ} (hi : i < len) (k : Claim) :
    pMinus k (run bytes len i, bytes i)
      = ((runSignals bytes len i).minusFlag && decide ((run bytes len i).claim = some k)) := by
  rw [runSignals_eq hi]; rfl

theorem pTrue_eq {i : ℕ} (hi : i < len) (k : Claim) :
    pTrue k (run bytes len i, bytes i)
      = ((runSignals bytes len i).trueDone && decide ((run bytes len i).claim = some k)) := by
  rw [runSignals_eq hi]; rfl

theorem fVal_eq {i : ℕ} (hi : i < len) :
    fVal (run bytes len i, bytes i) = (runSignals bytes len i).valOut := by
  rw [runSignals_eq hi]; rfl

/-- The trace of the accepting run over the first `len` bytes. -/
theorem trace_eq (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome) :
    traceL Regs.init (toL bytes len)
      = (List.range len).map fun i => (run bytes len i, bytes i) :=
  (run_toL hsteps len le_rfl).2

theorem presentCount_eq (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
    (k : Claim) :
    presentCount bytes len k
      = ((traceL Regs.init (toL bytes len)).filter (pMatch k)).length := by
  rw [trace_eq hsteps, filter_map_length, presentCount]
  congr 1
  refine List.filter_congr fun i hi => ?_
  rw [pMatch_eq (List.mem_range.mp hi)]

theorem signCount_eq (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
    (k : Claim) :
    signCount bytes len k
      = ((traceL Regs.init (toL bytes len)).filter (pMinus k)).length := by
  rw [trace_eq hsteps, filter_map_length, signCount]
  congr 1
  refine List.filter_congr fun i hi => ?_
  rw [pMinus_eq (List.mem_range.mp hi)]

theorem trueCount_eq (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
    (k : Claim) :
    trueCount bytes len k
      = ((traceL Regs.init (toL bytes len)).filter (pTrue k)).length := by
  rw [trace_eq hsteps, filter_map_length, trueCount]
  congr 1
  refine List.filter_congr fun i hi => ?_
  rw [pTrue_eq (List.mem_range.mp hi)]

/-- The values routed to claim `k`, in order. -/
def valsT (k : Claim) (T : List (Regs × ℕ)) : List ℕ := (T.filter (pEmit k)).map fVal

theorem slotLen_eq_valsT (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
    (k : Claim) :
    slotLen bytes len k = (valsT k (traceL Regs.init (toL bytes len))).length := by
  rw [valsT, trace_eq hsteps, List.length_map, filter_map_length, slotLen]
  congr 1
  refine List.filter_congr fun i hi => ?_
  have := pEmit_eq (bytes := bytes) (len := len) (List.mem_range.mp hi) k
  rw [this, RunTheory.emitsAt]

theorem valsT_eq (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
    (k : Claim) :
    valsT k (traceL Regs.init (toL bytes len))
      = ((List.range len).filter (RunTheory.emitsAt bytes len k)).map
          fun i => (runSignals bytes len i).valOut := by
  rw [valsT, trace_eq hsteps, filter_map_map]
  have h1 : ((List.range len).filter fun i => pEmit k (run bytes len i, bytes i))
      = (List.range len).filter (RunTheory.emitsAt bytes len k) :=
    List.filter_congr fun i hi => by rw [pEmit_eq (List.mem_range.mp hi)]
  rw [h1]
  refine List.map_congr_left fun i hi => ?_
  exact fVal_eq (List.mem_range.mp (List.mem_of_mem_filter hi))

theorem cell_eq_valsT (k : Claim)
    (hkind : Model.isStrClaim k = true ∨ Model.isIntClaim k = true)
    (hsteps : ∀ i, i < len → (step (run bytes len i) (bytes i)).isSome)
    (hpresent : presentCount bytes len k ≤ 1) (t : ℕ) :
    cell bytes len k t = (valsT k (traceL Regs.init (toL bytes len))).getD t 0 := by
  rw [valsT_eq hsteps]
  rcases Nat.lt_or_ge t (slotLen bytes len k) with ht | ht
  · obtain ⟨i, hi, hei, hofs⟩ := RunTheory.cover bytes len k hkind hsteps hpresent ht
    have hcell := RunTheory.cell_eq_valOut bytes len k hkind hsteps hpresent hi hei
    rw [hofs] at hcell
    rw [hcell]
    obtain ⟨l2, hl2⟩ := range_split hi
    rw [hl2]
    have hct : ((List.range i).filter (RunTheory.emitsAt bytes len k)).length = t := by
      have := RunTheory.ofs_eq_emitCount bytes len k hkind hsteps hpresent hi hei
      rw [hofs] at this
      exact this.symm
    rw [← hct]
    exact (getD_filter_map (RunTheory.emitsAt bytes len k)
      (fun i => (runSignals bytes len i).valOut) 0 (List.range i) i l2 hei).symm
  · rw [RunTheory.cell_eq_zero bytes len k hkind hsteps hpresent ht]
    have hlen : (((List.range len).filter (RunTheory.emitsAt bytes len k)).map
        fun i => (runSignals bytes len i).valOut).length ≤ t := by
      rw [List.length_map]
      exact le_trans (le_of_eq (RunTheory.slotLen_eq bytes len k).symm) ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
    rfl

end

end RunList

end Solution.JSONExtract
