import Solution.JSONExtract.SubAutomaton
import Solution.JSONExtract.MainAutomaton
import Solution.JSONExtract.AutomatonTheorems
import Solution.JSONExtract.OneHotInterface
import Solution.JSONExtract.Theorems
import Solution.JSONExtract.Model

/-!
# Reading the two automaton assertions at the model level (`JSONExtract`)

`SubAutomaton.Spec` and `MainAutomaton.Spec` are field-level statements: they say
each `next[j]` is `prev[j] + active · (mass_j − prev[j])`, where `mass_j` is a sum
of edge products.  This file identifies those masses with the model: at a one-hot
source state, with the byte-class flags of a concrete byte, the mass at target `j`
is the indicator that `Model.stepSub` / `Model.stepSt` lands on `j`.

The proofs are staged, because a one-shot `fin_cases s <;> fin_cases j` over the
`13 × 13` (resp. `27 × 27`) pairs exhausts the heartbeat budget:

* a generic *guarded chain* (`chainPick` / `chainMass`): the model steps are
  if-chains `if g₁ then some d₁ else if g₂ …`, and the mass is the sum of the
  guards of the edges into `j`.  `chainMass_eq_optInd` proves the two agree once
  and for all, given that the guards are pairwise exclusive (`Excl`);
* one lemma per source state, which unrolls the concrete edge fold into that
  state's chain and discharges the exclusivity of its guards on the byte ranges.
  The unrolling goes through the edge *list* (`foldl_ite_vector`): peeling
  `List.map`/`List.sum` over a literal list is linear, where peeling
  `Fin.foldl_succ` re-normalizes every index at every step (the same file took
  6 min 26 s that way and 8 s this way);
* the assembly, a `fin_cases` over the source state whose branches are one
  `exact` each.

The `b < 256` hypothesis of the two top-level theorems is not needed for the
proofs (the byte classes are disjoint on all of `ℕ`); it is kept so callers can
pass the byte bound they already have.
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open ByteClass (ind)

namespace AutomatonModel

open Model (nSub Sub nSt St)
open Specs.JSON (quote backslash lowerU lbrace rbrace colon comma minus dot digit0 lowerT
  lowerR lowerE lowerF lowerA lowerN)

/-! ## Guarded chains -/

/-- The successor a guarded chain picks: the first true guard wins, and an
exhausted chain is a rejection. -/
def chainPick {n : ℕ} : List (Bool × Fin n) → Option (Fin n)
  | [] => none
  | (g, d) :: t => if g then some d else chainPick t

/-- The mass a guarded chain puts on `j`: the sum of the guards of its edges
into `j`. -/
def chainMass {n : ℕ} (l : List (Bool × Fin n)) (j : ℕ) : F circomPrime :=
  (l.map fun p => if p.2.val = j then ind p.1 else 0).sum

@[simp] lemma chainMass_nil {n : ℕ} (j : ℕ) : chainMass ([] : List (Bool × Fin n)) j = 0 := rfl

@[simp] lemma chainMass_cons {n : ℕ} (g : Bool) (d : Fin n) (t : List (Bool × Fin n)) (j : ℕ) :
    chainMass ((g, d) :: t) j = (if d.val = j then ind g else 0) + chainMass t j := by
  simp only [chainMass, List.map_cons, List.sum_cons]

/-- The guards of a chain are pairwise exclusive: no guard can be true together
with a later one. -/
def Excl {n : ℕ} : List (Bool × Fin n) → Prop
  | [] => True
  | (g, _) :: t => (∀ p ∈ t, (g && p.1) = false) ∧ Excl t

/-- A chain whose guards are all false puts no mass anywhere. -/
lemma chainMass_of_all_false {n : ℕ} :
    ∀ (l : List (Bool × Fin n)), (∀ p ∈ l, p.1 = false) → ∀ j : ℕ, chainMass l j = 0
  | [], _, _ => rfl
  | (g, d) :: t, h, j => by
    have hg : g = false := h (g, d) (List.mem_cons_self ..)
    rw [chainMass_cons, hg, chainMass_of_all_false t (fun p hp => h p (List.mem_cons_of_mem _ hp)) j]
    simp [ind]

/-- **The chain lemma.** With pairwise exclusive guards, the mass a chain puts on
`j` is the indicator that the chain picks `j`. -/
theorem chainMass_eq_optInd {n : ℕ} :
    ∀ (l : List (Bool × Fin n)), Excl l → ∀ j : Fin n, chainMass l j.val = optInd (chainPick l) j
  | [], _, j => by simp [chainPick]
  | (g, d) :: t, h, j => by
    rw [chainMass_cons, chainPick]
    cases g with
    | false =>
      rw [chainMass_eq_optInd t h.2 j]
      simp [ind]
    | true =>
      rw [chainMass_of_all_false t (fun p hp => by simpa using h.1 p hp) j.val,
        if_pos rfl, optInd_some]
      simp only [ind, if_true, add_zero]
      by_cases hd : d = j
      · rw [if_pos hd, if_pos (by rw [hd])]
      · rw [if_neg hd, if_neg (fun hh => hd (Fin.val_injective hh))]

/-! ## The one-hot source vector -/

/-- The one-hot indicator of a state, as an index rather than a field value. -/
def ohFin {n : ℕ} (s : Fin n) : Vector (F circomPrime) n :=
  Vector.ofFn fun i => if i = s then 1 else 0

/-- `ohOf` at (the field image of) a state index is `ohFin`. -/
lemma ohOf_eq_ohFin {n : ℕ} (hn : n < circomPrime) (s : Fin n) :
    ohOf n ((s.val : ℕ) : F circomPrime) = ohFin s := by
  have hval : (((s.val : ℕ) : F circomPrime)).val = s.val :=
    ZMod.val_natCast_of_lt (lt_trans s.isLt hn)
  refine Vector.ext fun i hi => ?_
  simp only [ohOf, ohFin, Vector.getElem_ofFn, hval]
  by_cases h : i = s.val
  · rw [if_pos h, if_pos (Fin.ext h)]
  · rw [if_neg h, if_neg (fun hh => h (congrArg Fin.val hh))]


/-! ## Unfolding tactics -/

/-- Reduce a guard-exclusivity goal to linear arithmetic on the byte. -/
macro "excl_tac" : tactic => `(tactic|
  (simp only [Excl, List.mem_cons, List.not_mem_nil, or_false, false_or, forall_eq_or_imp,
      forall_eq, forall_const, and_true, true_and, and_self, IsEmpty.forall_iff,
      Model.isWs, Model.isDigit, Model.isDigitNz, Model.isUpperHex, Model.isLowerHex, Model.isHex,
      Model.isUnescaped, Model.isSimpleEsc, Model.isExpLetter, Model.isSign, Model.isCont,
      Model.isLead2, Model.isLead3, Model.isLead4, Model.isContA0BF, Model.isCont809F,
      Model.isCont90BF, Model.isCont808F,
      Specs.JSON.space, Specs.JSON.tab, Specs.JSON.lf, Specs.JSON.cr, Specs.JSON.quote,
      Specs.JSON.backslash, Specs.JSON.slash, Specs.JSON.lbrace, Specs.JSON.rbrace,
      Specs.JSON.colon, Specs.JSON.comma, Specs.JSON.minus, Specs.JSON.plus, Specs.JSON.dot,
      Specs.JSON.digit0, Specs.JSON.digit9, Specs.JSON.upperA, Specs.JSON.upperE,
      Specs.JSON.upperF, Specs.JSON.lowerA, Specs.JSON.lowerB, Specs.JSON.lowerE,
      Specs.JSON.lowerF, Specs.JSON.lowerN, Specs.JSON.lowerR, Specs.JSON.lowerT,
      Specs.JSON.lowerU,
      Bool.and_eq_false_iff, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_false_iff,
      Bool.not_eq_true, Bool.not_eq_false, bne_iff_ne, beq_iff_eq, decide_eq_true_eq,
      decide_eq_false_iff_not, ne_eq, beq_eq_false_iff_ne, bne_eq_false_iff_eq];
   all_goals omega))

/-- `Fin.foldl` is a `List.foldl` over `List.finRange`. -/
lemma fin_foldl_eq_foldl_finRange {α : Type*} {n : ℕ} (f : α → Fin n → α) (x : α) :
    Fin.foldl n f x = (List.finRange n).foldl f x := by
  induction n generalizing x with
  | zero => rw [Fin.foldl_zero, List.finRange_zero, List.foldl_nil]
  | succ n ih => rw [Fin.foldl_succ, ih, List.finRange_succ, List.foldl_cons, List.foldl_map]

/-- Indexing a vector along `List.finRange` gives its list. -/
lemma map_finRange_getElem {α : Type*} {m : ℕ} (E : Vector α m) :
    (List.finRange m).map (fun i : Fin m => E[i.val]'i.isLt) = E.toList := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- A `List.foldl` of additions is the sum of its summands. -/
lemma foldl_add_list {M : Type*} [AddCommMonoid M] {α : Type*} (g : α → M) :
    ∀ (l : List α) (init : M), l.foldl (fun acc x => acc + g x) init = init + (l.map g).sum
  | [], init => by simp
  | x :: t, init => by
    rw [List.foldl_cons, foldl_add_list g t, List.map_cons, List.sum_cons]
    abel

/-- A filtered `Fin.foldl` indexing into a vector is the sum over that vector's
list.  Unrolling a `List.map`/`List.sum` over a concrete list is linear, where
peeling `Fin.foldl_succ` re-normalizes every index at every step. -/
lemma foldl_ite_vector {M : Type*} [AddCommMonoid M] {α : Type*} {m : ℕ} (E : Vector α m)
    (P : α → Prop) [DecidablePred P] (f : α → M) :
    Fin.foldl m (fun acc (e : Fin m) =>
        if P (E[e.val]'e.isLt) then acc + f (E[e.val]'e.isLt) else acc) 0
      = (E.toList.map fun x => if P x then f x else 0).sum := by
  rw [show (fun (acc : M) (e : Fin m) =>
        if P (E[e.val]'e.isLt) then acc + f (E[e.val]'e.isLt) else acc)
      = (fun (acc : M) (e : Fin m) =>
        acc + if P (E[e.val]'e.isLt) then f (E[e.val]'e.isLt) else 0) from by
    funext acc e; split <;> simp]
  rw [fin_foldl_eq_foldl_finRange, foldl_add_list, zero_add, ← map_finRange_getElem E,
    List.map_map]
  rfl

/-! ## The string sub-automaton -/

/-- The byte predicate an edge class of the sub-automaton reads. -/
def subGuard (b : ℕ) : SubAutomaton.SCls → Bool
  | .quote => b == quote | .unescaped => Model.isUnescaped b
  | .backslash => b == backslash | .lead2 => Model.isLead2 b | .e0 => b == 0xE0
  | .lead3 => Model.isLead3 b | .ed => b == 0xED | .f0 => b == 0xF0
  | .lead4 => Model.isLead4 b | .f4 => b == 0xF4 | .simpleEsc => Model.isSimpleEsc b
  | .lowerU => b == lowerU | .hex => Model.isHex b | .cont => Model.isCont b
  | .contA0BF => Model.isContA0BF b | .cont809F => Model.isCont809F b
  | .cont90BF => Model.isCont90BF b | .cont808F => Model.isCont808F b

/-- Every class flag of `classesOf b` is the indicator of its byte predicate. -/
lemma clsVal_classesOf (b : ℕ) (c : SubAutomaton.SCls) :
    SubAutomaton.clsVal (classesOf b) c = ind (subGuard b c) := by
  cases c <;> rfl


/-- The sub-automaton's mass as a sum over the edge list. -/
lemma massVal_list (c : ByteClass.Outputs (F circomPrime)) (prev : Vector (F circomPrime) nSub)
    (j : ℕ) :
    SubAutomaton.massVal c prev j
      = (SubAutomaton.edges.toList.map fun e =>
          if e.dst.val = j then prev[e.src.val]'e.src.isLt * SubAutomaton.clsVal c e.cls
          else 0).sum :=
  foldl_ite_vector SubAutomaton.edges (fun e => e.dst.val = j)
    (fun e => prev[e.src.val]'e.src.isLt * SubAutomaton.clsVal c e.cls)

/-- Unroll the 23-edge mass sum at a concrete source state into that state's chain. -/
macro "sub_mass_tac" : tactic => `(tactic|
  (simp +decide only [massVal_list, SubAutomaton.edges, Vector.toList_mk, 
     List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ohFin, Vector.getElem_ofFn,
     Fin.isValue, clsVal_classesOf, subGuard, if_true, if_false, one_mul, zero_mul,
     ite_self, add_zero, zero_add, chainMass];
   all_goals ring))

/-- The three facts a source state needs, assembled by the chain lemma. -/
lemma sub_of_chain {b : ℕ} {s : Sub} (L : List (Bool × Sub))
    (hm : ∀ j : Fin nSub, SubAutomaton.massVal (classesOf b) (ohFin s) j.val = chainMass L j.val)
    (hp : Model.stepSub true s b = chainPick L) (he : Excl L) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin s) j.val = optInd (Model.stepSub true s b) j := by
  rw [hm j, hp, chainMass_eq_optInd L he]

/-- The edges leaving `PLAIN`. -/
lemma massVal_PLAIN (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.PLAIN) j.val
      = optInd (Model.stepSub true Model.Sub.PLAIN b) j :=
  sub_of_chain [(b == quote, Model.Sub.PLAIN), (Model.isUnescaped b, Model.Sub.PLAIN),
      (b == backslash, Model.Sub.ESC), (Model.isLead2 b, Model.Sub.C1),
      (b == 0xE0, Model.Sub.E0s), (Model.isLead3 b, Model.Sub.C2),
      (b == 0xED, Model.Sub.EDs), (b == 0xF0, Model.Sub.F0s),
      (Model.isLead4 b, Model.Sub.C3), (b == 0xF4, Model.Sub.F4s)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `ESC`. -/
lemma massVal_ESC (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.ESC) j.val
      = optInd (Model.stepSub true Model.Sub.ESC b) j :=
  sub_of_chain [(Model.isSimpleEsc b, Model.Sub.PLAIN), (b == lowerU, Model.Sub.H1)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `H1`. -/
lemma massVal_H1 (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.H1) j.val
      = optInd (Model.stepSub true Model.Sub.H1 b) j :=
  sub_of_chain [(Model.isHex b, Model.Sub.H2)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `H2`. -/
lemma massVal_H2 (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.H2) j.val
      = optInd (Model.stepSub true Model.Sub.H2 b) j :=
  sub_of_chain [(Model.isHex b, Model.Sub.H3)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `H3`. -/
lemma massVal_H3 (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.H3) j.val
      = optInd (Model.stepSub true Model.Sub.H3 b) j :=
  sub_of_chain [(Model.isHex b, Model.Sub.H4)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `H4`. -/
lemma massVal_H4 (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.H4) j.val
      = optInd (Model.stepSub true Model.Sub.H4 b) j :=
  sub_of_chain [(Model.isHex b, Model.Sub.PLAIN)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `C1`. -/
lemma massVal_C1 (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.C1) j.val
      = optInd (Model.stepSub true Model.Sub.C1 b) j :=
  sub_of_chain [(Model.isCont b, Model.Sub.PLAIN)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `C2`. -/
lemma massVal_C2 (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.C2) j.val
      = optInd (Model.stepSub true Model.Sub.C2 b) j :=
  sub_of_chain [(Model.isCont b, Model.Sub.C1)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `C3`. -/
lemma massVal_C3 (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.C3) j.val
      = optInd (Model.stepSub true Model.Sub.C3 b) j :=
  sub_of_chain [(Model.isCont b, Model.Sub.C2)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `E0s`. -/
lemma massVal_E0s (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.E0s) j.val
      = optInd (Model.stepSub true Model.Sub.E0s b) j :=
  sub_of_chain [(Model.isContA0BF b, Model.Sub.C1)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `EDs`. -/
lemma massVal_EDs (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.EDs) j.val
      = optInd (Model.stepSub true Model.Sub.EDs b) j :=
  sub_of_chain [(Model.isCont809F b, Model.Sub.C1)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `F0s`. -/
lemma massVal_F0s (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.F0s) j.val
      = optInd (Model.stepSub true Model.Sub.F0s b) j :=
  sub_of_chain [(Model.isCont90BF b, Model.Sub.C2)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `F4s`. -/
lemma massVal_F4s (b : ℕ) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohFin Model.Sub.F4s) j.val
      = optInd (Model.stepSub true Model.Sub.F4s b) j :=
  sub_of_chain [(Model.isCont808F b, Model.Sub.C2)]
    (fun _ => by sub_mass_tac) rfl (by excl_tac) j

/-- **The sub-automaton's mass is the model step.**  At a one-hot source state,
with the byte-class flags of `b`, the transition mass at `j` is the indicator
that `Model.stepSub` (inside a string) lands on `j`. -/
theorem massVal_eq (b : ℕ) (hb : b < 256) (s : Sub) (j : Fin nSub) :
    SubAutomaton.massVal (classesOf b) (ohOf nSub ((s.val : ℕ) : F circomPrime)) j.val
      = optInd (Model.stepSub true s b) j := by
  rw [ohOf_eq_ohFin (ByteClass.lt_circomPrime (by norm_num)) s]
  fin_cases s
  · exact massVal_PLAIN b j
  · exact massVal_ESC b j
  · exact massVal_H1 b j
  · exact massVal_H2 b j
  · exact massVal_H3 b j
  · exact massVal_H4 b j
  · exact massVal_C1 b j
  · exact massVal_C2 b j
  · exact massVal_C3 b j
  · exact massVal_E0s b j
  · exact massVal_EDs b j
  · exact massVal_F0s b j
  · exact massVal_F4s b j

/-! ## The main automaton -/

/-- The byte predicate an edge class of the main automaton reads.  `subPlain`
says the sub-state before the byte is `PLAIN`, so a `"` closes a string. -/
def mainGuard (b : ℕ) (subPlain : Bool) : MainAutomaton.Cls → Bool
  | .ws => Model.isWs b | .lbrace => b == lbrace | .rbrace => b == rbrace
  | .quote => b == quote | .closeQuote => (b == quote) && subPlain
  | .notCloseQuote => !((b == quote) && subPlain)
  | .colon => b == colon | .comma => b == comma | .minus => b == minus
  | .zero => b == digit0 | .digitNz => Model.isDigitNz b | .digit => Model.isDigit b
  | .dot => b == dot | .expLetter => Model.isExpLetter b | .sign => Model.isSign b
  | .lowerT => b == lowerT | .lowerR => b == lowerR | .lowerU => b == lowerU
  | .lowerE => b == lowerE | .lowerF => b == lowerF | .lowerA => b == lowerA
  | .lowerL => b == 0x6C | .lowerS => b == 0x73 | .lowerN => b == lowerN

/-- Every class flag of `classesOf b`, read with the materialized `closeQuote`,
is the indicator of its byte predicate. -/
lemma clsVal_main_classesOf (b : ℕ) (subPlain : Bool) (c : MainAutomaton.Cls) :
    MainAutomaton.clsVal (classesOf b) (ind ((b == quote) && subPlain)) c
      = ind (mainGuard b subPlain c) := by
  cases c <;> first | rfl | simp only [MainAutomaton.clsVal, mainGuard, ByteClass.one_sub_ind]

/-- The `(str, int, bool, unk)` flag vector of a kind. -/
def kindsOf (k : Model.Kind) : Vector (F circomPrime) 4 :=
  #v[ind (decide (k = Model.Kind.str)), ind (decide (k = Model.Kind.int)),
     ind (decide (k = Model.Kind.bool)), ind (decide (k = Model.Kind.unk))]

/-- The kind condition a type gate reads. -/
def gateGuard (k : Model.Kind) : MainAutomaton.Gate → Bool
  | .strOrUnk => decide (k = Model.Kind.str) || decide (k = Model.Kind.unk)
  | .intOrUnk => decide (k = Model.Kind.int) || decide (k = Model.Kind.unk)
  | .boolOrUnk => decide (k = Model.Kind.bool) || decide (k = Model.Kind.unk)
  | .unk => decide (k = Model.Kind.unk)

/-- Each type gate of `kindsOf k` is the indicator of its kind condition. -/
lemma gateVal_kindsOf (k : Model.Kind) (g : MainAutomaton.Gate) :
    MainAutomaton.gateVal (kindsOf k) g = ind (gateGuard k g) := by
  cases k <;> cases g <;>
    simp [MainAutomaton.gateVal, kindsOf, gateGuard, ByteClass.ind]


/-- The main automaton's ungated mass as a sum over the edge list. -/
lemma plainMassVal_list (c : ByteClass.Outputs (F circomPrime)) (cq : F circomPrime)
    (prev : Vector (F circomPrime) nSt) (j : ℕ) :
    MainAutomaton.plainMassVal c cq prev j
      = (MainAutomaton.plainEdges.toList.map fun e =>
          if e.dst.val = j then prev[e.src.val]'e.src.isLt * MainAutomaton.clsVal c cq e.cls
          else 0).sum :=
  foldl_ite_vector MainAutomaton.plainEdges (fun e => e.dst.val = j)
    (fun e => prev[e.src.val]'e.src.isLt * MainAutomaton.clsVal c cq e.cls)

/-- The main automaton's gated mass as a sum over the edge list. -/
lemma gatedMassVal_list (c : ByteClass.Outputs (F circomPrime)) (cq : F circomPrime)
    (kinds : Vector (F circomPrime) 4) (prev : Vector (F circomPrime) nSt) (j : ℕ) :
    MainAutomaton.gatedMassVal c cq kinds prev j
      = (MainAutomaton.gatedEdges.toList.map fun e =>
          if e.dst.val = j then prev[e.src.val]'e.src.isLt * MainAutomaton.clsVal c cq e.cls
            * MainAutomaton.gateVal kinds e.gate
          else 0).sum :=
  foldl_ite_vector MainAutomaton.gatedEdges (fun e => e.dst.val = j)
    (fun e => prev[e.src.val]'e.src.isLt * MainAutomaton.clsVal c cq e.cls
      * MainAutomaton.gateVal kinds e.gate)

/-- Unroll the 50- and 11-edge mass sums at a concrete source state into that
state's chain. -/
macro "main_mass_tac" : tactic => `(tactic|
  (simp +decide only [plainMassVal_list, gatedMassVal_list, MainAutomaton.plainEdges,
     MainAutomaton.gatedEdges, Vector.toList_mk, 
     List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ohFin, Vector.getElem_ofFn,
     Fin.isValue, clsVal_main_classesOf, mainGuard, gateVal_kindsOf, gateGuard,
     ByteClass.ind_mul, if_true, if_false, one_mul, zero_mul, ite_self, add_zero, zero_add,
     chainMass];
   all_goals ring))

/-- The three facts a source state needs, assembled by the chain lemma. -/
lemma main_of_chain {b : ℕ} {kind : Model.Kind} {subPlain : Bool} {s : St}
    (L : List (Bool × St))
    (hm : ∀ j : Fin nSt,
      MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain)) (ohFin s) j.val
        + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
          (ohFin s) j.val = chainMass L j.val)
    (hp : Model.stepSt kind subPlain s b = chainPick L) (he : Excl L) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain)) (ohFin s) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin s) j.val = optInd (Model.stepSt kind subPlain s b) j := by
  rw [hm j, hp, chainMass_eq_optInd L he]

/-- The edges leaving `PRE`. -/
lemma mainMass_PRE (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.PRE) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.PRE) j.val
      = optInd (Model.stepSt kind subPlain Model.St.PRE b) j :=
  main_of_chain
    [(Model.isWs b, Model.St.PRE), (b == lbrace, Model.St.OBJ)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `OBJ`. -/
lemma mainMass_OBJ (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.OBJ) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.OBJ) j.val
      = optInd (Model.stepSt kind subPlain Model.St.OBJ b) j :=
  main_of_chain
    [(Model.isWs b, Model.St.OBJ), (b == quote, Model.St.KEY), (b == rbrace, Model.St.END)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `KEY`. -/
lemma mainMass_KEY (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.KEY) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.KEY) j.val
      = optInd (Model.stepSt kind subPlain Model.St.KEY b) j :=
  main_of_chain
    [(((b == quote) && subPlain), Model.St.AKEY), (!((b == quote) && subPlain), Model.St.KEY)]
    (fun _ => by main_mass_tac)
    (by
      have hst : Model.stepSt kind subPlain Model.St.KEY b
          = if ((b == quote) && subPlain) = true then some Model.St.AKEY
            else some Model.St.KEY := rfl
      rw [hst]
      cases hq : ((b == quote) && subPlain) <;> simp [chainPick, hq])
    (by
      refine ⟨fun p hp => ?_, fun p hp => absurd hp (by simp), trivial⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact Bool.and_not_self _) j

/-- The edges leaving `AKEY`. -/
lemma mainMass_AKEY (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.AKEY) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.AKEY) j.val
      = optInd (Model.stepSt kind subPlain Model.St.AKEY b) j :=
  main_of_chain
    [(Model.isWs b, Model.St.AKEY), (b == colon, Model.St.PVAL)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `PVAL`. -/
lemma mainMass_PVAL (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.PVAL) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.PVAL) j.val
      = optInd (Model.stepSt kind subPlain Model.St.PVAL b) j :=
  main_of_chain
    [(Model.isWs b, Model.St.PVAL),
      ((b == quote) && (decide (kind = Model.Kind.str) || decide (kind = Model.Kind.unk)), Model.St.STR),
      ((b == minus) && (decide (kind = Model.Kind.int) || decide (kind = Model.Kind.unk)), Model.St.NSIGN),
      ((b == digit0) && (decide (kind = Model.Kind.int) || decide (kind = Model.Kind.unk)), Model.St.NZERO),
      (Model.isDigitNz b && (decide (kind = Model.Kind.int) || decide (kind = Model.Kind.unk)), Model.St.NINT),
      ((b == lowerT) && (decide (kind = Model.Kind.bool) || decide (kind = Model.Kind.unk)), Model.St.T1),
      ((b == lowerF) && (decide (kind = Model.Kind.bool) || decide (kind = Model.Kind.unk)), Model.St.F1),
      ((b == lowerN) && decide (kind = Model.Kind.unk), Model.St.N1)]
    (fun _ => by main_mass_tac) rfl (by cases kind <;> excl_tac) j

/-- The edges leaving `STR`. -/
lemma mainMass_STR (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.STR) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.STR) j.val
      = optInd (Model.stepSt kind subPlain Model.St.STR b) j :=
  main_of_chain
    [(((b == quote) && subPlain), Model.St.AVAL), (!((b == quote) && subPlain), Model.St.STR)]
    (fun _ => by main_mass_tac)
    (by
      have hst : Model.stepSt kind subPlain Model.St.STR b
          = if ((b == quote) && subPlain) = true then some Model.St.AVAL
            else some Model.St.STR := rfl
      rw [hst]
      cases hq : ((b == quote) && subPlain) <;> simp [chainPick, hq])
    (by
      refine ⟨fun p hp => ?_, fun p hp => absurd hp (by simp), trivial⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact Bool.and_not_self _) j

/-- The edges leaving `NSIGN`. -/
lemma mainMass_NSIGN (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.NSIGN) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.NSIGN) j.val
      = optInd (Model.stepSt kind subPlain Model.St.NSIGN b) j :=
  main_of_chain
    [(b == digit0, Model.St.NZERO), (Model.isDigitNz b, Model.St.NINT)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `NZERO`. -/
lemma mainMass_NZERO (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.NZERO) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.NZERO) j.val
      = optInd (Model.stepSt kind subPlain Model.St.NZERO b) j :=
  main_of_chain
    [((b == dot) && decide (kind = Model.Kind.unk), Model.St.NDOT),
      (Model.isExpLetter b && decide (kind = Model.Kind.unk), Model.St.NE),
      (Model.isWs b, Model.St.AVAL), (b == comma, Model.St.SEP), (b == rbrace, Model.St.END)]
    (fun _ => by main_mass_tac) rfl (by cases kind <;> excl_tac) j

/-- The edges leaving `NINT`. -/
lemma mainMass_NINT (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.NINT) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.NINT) j.val
      = optInd (Model.stepSt kind subPlain Model.St.NINT b) j :=
  main_of_chain
    [(Model.isDigit b, Model.St.NINT),
      ((b == dot) && decide (kind = Model.Kind.unk), Model.St.NDOT),
      (Model.isExpLetter b && decide (kind = Model.Kind.unk), Model.St.NE),
      (Model.isWs b, Model.St.AVAL), (b == comma, Model.St.SEP), (b == rbrace, Model.St.END)]
    (fun _ => by main_mass_tac) rfl (by cases kind <;> excl_tac) j

/-- The edges leaving `NDOT`. -/
lemma mainMass_NDOT (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.NDOT) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.NDOT) j.val
      = optInd (Model.stepSt kind subPlain Model.St.NDOT b) j :=
  main_of_chain
    [(Model.isDigit b, Model.St.NFRAC)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `NFRAC`. -/
lemma mainMass_NFRAC (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.NFRAC) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.NFRAC) j.val
      = optInd (Model.stepSt kind subPlain Model.St.NFRAC b) j :=
  main_of_chain
    [(Model.isDigit b, Model.St.NFRAC), (Model.isExpLetter b, Model.St.NE),
      (Model.isWs b, Model.St.AVAL), (b == comma, Model.St.SEP), (b == rbrace, Model.St.END)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `NE`. -/
lemma mainMass_NE (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.NE) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.NE) j.val
      = optInd (Model.stepSt kind subPlain Model.St.NE b) j :=
  main_of_chain
    [(Model.isSign b, Model.St.NESIGN), (Model.isDigit b, Model.St.NEXP)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `NESIGN`. -/
lemma mainMass_NESIGN (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.NESIGN) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.NESIGN) j.val
      = optInd (Model.stepSt kind subPlain Model.St.NESIGN b) j :=
  main_of_chain
    [(Model.isDigit b, Model.St.NEXP)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `NEXP`. -/
lemma mainMass_NEXP (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.NEXP) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.NEXP) j.val
      = optInd (Model.stepSt kind subPlain Model.St.NEXP b) j :=
  main_of_chain
    [(Model.isDigit b, Model.St.NEXP), (Model.isWs b, Model.St.AVAL),
      (b == comma, Model.St.SEP), (b == rbrace, Model.St.END)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `T1`. -/
lemma mainMass_T1 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.T1) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.T1) j.val
      = optInd (Model.stepSt kind subPlain Model.St.T1 b) j :=
  main_of_chain
    [(b == lowerR, Model.St.T2)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `T2`. -/
lemma mainMass_T2 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.T2) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.T2) j.val
      = optInd (Model.stepSt kind subPlain Model.St.T2 b) j :=
  main_of_chain
    [(b == lowerU, Model.St.T3)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `T3`. -/
lemma mainMass_T3 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.T3) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.T3) j.val
      = optInd (Model.stepSt kind subPlain Model.St.T3 b) j :=
  main_of_chain
    [(b == lowerE, Model.St.AVAL)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `F1`. -/
lemma mainMass_F1 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.F1) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.F1) j.val
      = optInd (Model.stepSt kind subPlain Model.St.F1 b) j :=
  main_of_chain
    [(b == lowerA, Model.St.F2)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `F2`. -/
lemma mainMass_F2 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.F2) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.F2) j.val
      = optInd (Model.stepSt kind subPlain Model.St.F2 b) j :=
  main_of_chain
    [(b == 0x6C, Model.St.F3)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `F3`. -/
lemma mainMass_F3 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.F3) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.F3) j.val
      = optInd (Model.stepSt kind subPlain Model.St.F3 b) j :=
  main_of_chain
    [(b == 0x73, Model.St.F4)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `F4`. -/
lemma mainMass_F4 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.F4) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.F4) j.val
      = optInd (Model.stepSt kind subPlain Model.St.F4 b) j :=
  main_of_chain
    [(b == lowerE, Model.St.AVAL)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `N1`. -/
lemma mainMass_N1 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.N1) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.N1) j.val
      = optInd (Model.stepSt kind subPlain Model.St.N1 b) j :=
  main_of_chain
    [(b == lowerU, Model.St.N2)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `N2`. -/
lemma mainMass_N2 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.N2) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.N2) j.val
      = optInd (Model.stepSt kind subPlain Model.St.N2 b) j :=
  main_of_chain
    [(b == 0x6C, Model.St.N3)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `N3`. -/
lemma mainMass_N3 (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.N3) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.N3) j.val
      = optInd (Model.stepSt kind subPlain Model.St.N3 b) j :=
  main_of_chain
    [(b == 0x6C, Model.St.AVAL)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `AVAL`. -/
lemma mainMass_AVAL (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.AVAL) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.AVAL) j.val
      = optInd (Model.stepSt kind subPlain Model.St.AVAL b) j :=
  main_of_chain
    [(Model.isWs b, Model.St.AVAL), (b == comma, Model.St.SEP), (b == rbrace, Model.St.END)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `SEP`. -/
lemma mainMass_SEP (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.SEP) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.SEP) j.val
      = optInd (Model.stepSt kind subPlain Model.St.SEP b) j :=
  main_of_chain
    [(Model.isWs b, Model.St.SEP), (b == quote, Model.St.KEY)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- The edges leaving `END`. -/
lemma mainMass_END (b : ℕ) (kind : Model.Kind) (subPlain : Bool) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) (ind ((b == quote) && subPlain))
        (ohFin Model.St.END) j.val
      + MainAutomaton.gatedMassVal (classesOf b) (ind ((b == quote) && subPlain)) (kindsOf kind)
        (ohFin Model.St.END) j.val
      = optInd (Model.stepSt kind subPlain Model.St.END b) j :=
  main_of_chain
    [(Model.isWs b, Model.St.END)]
    (fun _ => by main_mass_tac) rfl (by excl_tac) j

/-- **The main automaton's mass is the model step.**  At a one-hot source state,
with the byte-class flags of `b`, the materialized `closeQuote` and the kind
flags of the claim register, the transition mass at `j` is the indicator that
`Model.stepSt` lands on `j`. -/
theorem mainMass_eq (b : ℕ) (hb : b < 256) (s : St) (kind : Model.Kind) (subPlain : Bool)
    (cq : F circomPrime) (hcq : cq = ind ((b == quote) && subPlain)) (j : Fin nSt) :
    MainAutomaton.plainMassVal (classesOf b) cq (ohOf nSt ((s.val : ℕ) : F circomPrime)) j.val
      + MainAutomaton.gatedMassVal (classesOf b) cq (kindsOf kind)
        (ohOf nSt ((s.val : ℕ) : F circomPrime)) j.val
      = optInd (Model.stepSt kind subPlain s b) j := by
  subst hcq
  rw [ohOf_eq_ohFin (ByteClass.lt_circomPrime (by norm_num)) s]
  fin_cases s
  · exact mainMass_PRE b kind subPlain j
  · exact mainMass_OBJ b kind subPlain j
  · exact mainMass_KEY b kind subPlain j
  · exact mainMass_AKEY b kind subPlain j
  · exact mainMass_PVAL b kind subPlain j
  · exact mainMass_STR b kind subPlain j
  · exact mainMass_NSIGN b kind subPlain j
  · exact mainMass_NZERO b kind subPlain j
  · exact mainMass_NINT b kind subPlain j
  · exact mainMass_NDOT b kind subPlain j
  · exact mainMass_NFRAC b kind subPlain j
  · exact mainMass_NE b kind subPlain j
  · exact mainMass_NESIGN b kind subPlain j
  · exact mainMass_NEXP b kind subPlain j
  · exact mainMass_T1 b kind subPlain j
  · exact mainMass_T2 b kind subPlain j
  · exact mainMass_T3 b kind subPlain j
  · exact mainMass_F1 b kind subPlain j
  · exact mainMass_F2 b kind subPlain j
  · exact mainMass_F3 b kind subPlain j
  · exact mainMass_F4 b kind subPlain j
  · exact mainMass_N1 b kind subPlain j
  · exact mainMass_N2 b kind subPlain j
  · exact mainMass_N3 b kind subPlain j
  · exact mainMass_AVAL b kind subPlain j
  · exact mainMass_SEP b kind subPlain j
  · exact mainMass_END b kind subPlain j

/-! ## What the two `Spec`s say at an active position -/

/-- With `active = 1`, a one-hot source state and the byte classes of `b`, the
sub-automaton's row pins the witnessed next state to the model's step. -/
theorem subNext_of_active {inp : SubAutomaton.Inputs (F circomPrime)} (b : ℕ) (hb : b < 256)
    (s : Sub) (inStr : Bool) (hcls : inp.cls = classesOf b)
    (hprev : inp.subPrev = ohOf nSub ((s.val : ℕ) : F circomPrime))
    (hinStr : inp.inStr = ind inStr) (hact : inp.active = 1)
    (h : SubAutomaton.Spec inp) (j : Fin nSub) :
    inp.subNext[j] = optInd (Model.stepSub inStr s b) j := by
  obtain ⟨-, -, hrow⟩ := h
  rw [hrow j, hcls, hprev, hinStr, hact, one_mul]
  cases inStr with
  | true =>
    rw [ByteClass.ind_true, massVal_eq b hb s j]
    simp only [sub_self, ite_self, add_zero, one_mul]
    ring
  | false =>
    rw [ByteClass.ind_false, show Model.stepSub false s b = some Model.Sub.PLAIN from rfl,
      optInd_some]
    by_cases hj : (j : ℕ) = 0
    · rw [if_pos hj, if_pos (Fin.ext (n := nSub) hj.symm)]
      ring
    · rw [if_neg hj, if_neg (fun hh : Model.Sub.PLAIN = j => hj (by rw [← hh]; rfl))]
      ring

/-- With `active = 0` the sub-state is frozen. -/
theorem subNext_of_inactive {inp : SubAutomaton.Inputs (F circomPrime)} (hact : inp.active = 0)
    (h : SubAutomaton.Spec inp) (j : Fin nSub) : inp.subNext[j] = inp.subPrev[j] := by
  obtain ⟨-, -, hrow⟩ := h
  rw [hrow j, hact, zero_mul, add_zero]

/-- With `active = 1`, a one-hot source state, the byte classes of `b`, the
materialized `closeQuote` and the kind flags of the claim register, the main
automaton's row pins the witnessed next state to the model's step. -/
theorem stNext_of_active {inp : MainAutomaton.Inputs (F circomPrime)} (b : ℕ) (hb : b < 256)
    (s : St) (kind : Model.Kind) (subPlain : Bool) (hcls : inp.cls = classesOf b)
    (hcq : inp.closeQuote = ind ((b == quote) && subPlain))
    (hkinds : inp.kinds = kindsOf kind)
    (hprev : inp.stPrev = ohOf nSt ((s.val : ℕ) : F circomPrime))
    (hact : inp.active = 1) (h : MainAutomaton.Spec inp) (j : Fin nSt) :
    inp.stNext[j] = optInd (Model.stepSt kind subPlain s b) j := by
  obtain ⟨-, -, hrow⟩ := h
  rw [hrow j, hcls, hcq, hkinds, hprev, hact, one_mul,
    mainMass_eq b hb s kind subPlain _ rfl j]
  ring

/-- With `active = 0` the main state is frozen. -/
theorem stNext_of_inactive {inp : MainAutomaton.Inputs (F circomPrime)} (hact : inp.active = 0)
    (h : MainAutomaton.Spec inp) (j : Fin nSt) : inp.stNext[j] = inp.stPrev[j] := by
  obtain ⟨-, -, hrow⟩ := h
  rw [hrow j, hact, zero_mul, add_zero]

end AutomatonModel
end Solution.JSONExtract
