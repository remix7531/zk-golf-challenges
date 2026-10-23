import Solution.JSONExtract.ParseInv

/-!
# Inverting the combinator grammar (`JSONExtract`)

`SerParse.lean` runs the trusted grammar forward on a `Serial.Ser`; this file
runs it backwards.  Every combinator of `Challenge/Specs/Parser.lean` used by
the JSON grammar gets an inversion lemma "a successful parse decomposes its
input into the consumed token and the remainder", and the JSON grammar itself
is inverted down to the shape of a flat object: whitespace runs, string bodies
as lists of `Serial.SE`, numbers as `Serial.SNum`.

Everything here lives at the *code-point* level; the byte level is handled once
and for all by `ParseInv.bytesOfCps` (UTF-8 is canonical on what the decoder
accepts).
-/

namespace Solution.JSONExtract

namespace ParseInv

open Specs
open Specs.JSON
open Specs.Parser
open Serial
open SerParse

/-! ## Repetition -/

/-- `Chain p l as r`: running `p` repeatedly from `l` yields the values `as`
and leaves `r`.  This is the inversion of `manyUpTo`, in the shape an induction
over the parsed items wants. -/
inductive Chain {α : Type} (p : Parser α) : List ℕ → List α → List ℕ → Prop
  | nil (r : List ℕ) : Chain p r [] r
  | cons {l : List ℕ} {a : α} {r1 : List ℕ} {as : List α} {r : List ℕ} :
      p l = some (a, r1) → Chain p r1 as r → Chain p l (a :: as) r

theorem manyUpTo_chain {α : Type} {p : Parser α} : ∀ (n : ℕ) {l : List ℕ} {as : List α}
    {r : List ℕ}, manyUpTo n p l = some (as, r) → Chain p l as r := by
  intro n
  induction n with
  | zero =>
    intro l as r h
    simp only [manyUpTo_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil _
  | succ n ih =>
    intro l as r h
    rw [manyUpTo_succ] at h
    cases hp : p l with
    | none =>
      rw [hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .nil _
    | some ar =>
      obtain ⟨a, r1⟩ := ar
      rw [hp] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨as', r'⟩, hrec, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact .cons hp (ih hrec)

theorem many_chain {α : Type} {p : Parser α} {l : List ℕ} {as : List α} {r : List ℕ}
    (h : many p l = some (as, r)) : Chain p l as r := by
  rw [many_apply] at h
  exact manyUpTo_chain _ h

theorem sepByUpTo_inv {α : Type} {p : Parser α} {sep : Parser Unit} : ∀ (n : ℕ) {l : List ℕ}
    {as : List α} {r : List ℕ}, sepByUpTo n p sep l = some (as, r) →
    (as = [] ∧ r = l) ∨ (∃ a r1 as', as = a :: as' ∧ p l = some (a, r1) ∧
      Chain (sep *> p) r1 as' r) := by
  intro n
  cases n with
  | zero =>
    intro l as r h
    simp only [sepByUpTo_zero, Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨h.1.symm, h.2.symm⟩
  | succ n =>
    intro l as r h
    rw [sepByUpTo_succ] at h
    cases hp : p l with
    | none =>
      rw [hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨h.1.symm, h.2.symm⟩
    | some ar =>
      obtain ⟨a, r1⟩ := ar
      rw [hp] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨as', r'⟩, hrec, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact Or.inr ⟨a, r1, as', rfl, rfl, manyUpTo_chain _ hrec⟩

theorem sepBy_inv {α : Type} {p : Parser α} {sep : Parser Unit} {l : List ℕ} {as : List α}
    {r : List ℕ} (h : sepBy p sep l = some (as, r)) :
    (as = [] ∧ r = l) ∨ (∃ a r1 as', as = a :: as' ∧ p l = some (a, r1) ∧
      Chain (sep *> p) r1 as' r) := by
  rw [sepBy_apply] at h
  exact sepByUpTo_inv _ h

/-! ## The primitive combinators -/

theorem byte_inv {b : ℕ} {l r : List ℕ} (h : byte b l = some ((), r)) : l = b :: r := by
  cases l with
  | nil => simp at h
  | cons c t =>
    rw [byte_cons] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      next hc => rw [hc]
    · simp at h

theorem eof_inv {l r : List ℕ} (h : eof l = some ((), r)) : l = [] ∧ r = [] := by
  cases l with
  | nil => simp only [eof_nil, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨rfl, h.2.symm⟩
  | cons c t => simp at h

theorem optional_inv {α : Type} {p : Parser α} {l : List ℕ} {x : Option α} {r : List ℕ}
    (h : Parser.optional p l = some (x, r)) :
    (∃ a, x = some a ∧ p l = some (a, r)) ∨ (x = none ∧ r = l ∧ p l = none) := by
  rw [optional_apply] at h
  cases hp : p l with
  | none =>
    rw [hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inr ⟨h.1.symm, h.2.symm, rfl⟩
  | some ar =>
    obtain ⟨a, r'⟩ := ar
    rw [hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨a, h.1.symm, by rw [h.2]⟩

theorem literal_inv : ∀ (bs : List ℕ) {l r : List ℕ}, literal bs l = some ((), r) →
    l = bs ++ r := by
  intro bs
  induction bs with
  | nil =>
    intro l r h
    simp only [literal_nil, Option.some.injEq, Prod.mk.injEq] at h
    rw [List.nil_append, h.2]
  | cons b bs ih =>
    intro l r h
    rw [literal_cons] at h
    cases l with
    | nil => simp at h
    | cons c t =>
      rw [byte_cons] at h
      split at h
      · simp only [Option.bind_some] at h
        next hc => rw [hc, List.cons_append, ih h]
      · simp at h

/-! ## Whitespace -/

theorem takeWhile_mem {q : ℕ → Bool} : ∀ {l : List ℕ}, ∀ x ∈ l.takeWhile q, q x = true := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons c t ih =>
    intro x hx
    rw [List.takeWhile_cons] at hx
    split at hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · next hc => exact hc
      · exact ih x hx
    · simp at hx

theorem dropWhile_head {q : ℕ → Bool} : ∀ {l : List ℕ} {c : ℕ} {t : List ℕ},
    l.dropWhile q = c :: t → q c = false := by
  intro l
  induction l with
  | nil => intro c t h; simp at h
  | cons b l ih =>
    intro c t h
    rw [List.dropWhile_cons] at h
    split at h
    · exact ih h
    · next hb =>
      rw [List.cons.injEq] at h
      rw [← h.1]
      simpa using hb

theorem ws_inv {l r : List ℕ} (h : ws l = some ((), r)) :
    ∃ w, IsWs w ∧ l = w ++ r ∧ NotWs r := by
  rw [ws, skipWhile_apply, Option.some.injEq, Prod.mk.injEq] at h
  refine ⟨l.takeWhile Specs.JSON.isWs, ?_, ?_, ?_⟩
  · intro b hb; rw [isWs_eq]; exact takeWhile_mem b hb
  · rw [← h.2, List.takeWhile_append_dropWhile]
  · intro c t hc
    rw [← h.2] at hc
    exact dropWhile_head hc

/-! ## Sequencing -/

theorem bind_inv {α β : Type} {p : Parser α} {f : α → Parser β} {l : List ℕ} {x : β}
    {r : List ℕ} (h : (p >>= f) l = some (x, r)) :
    ∃ a r1, p l = some (a, r1) ∧ f a r1 = some (x, r) := by
  simp only [bind_apply, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r1⟩, h1, h2⟩ := h
  exact ⟨a, r1, h1, h2⟩

theorem seqRight_inv {α β : Type} {p : Parser α} {q : Parser β} {l : List ℕ} {x : β}
    {r : List ℕ} (h : (p *> q) l = some (x, r)) :
    ∃ a r1, p l = some (a, r1) ∧ q r1 = some (x, r) := by
  simp only [seqRight_apply, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r1⟩, h1, h2⟩ := h
  exact ⟨a, r1, h1, h2⟩

theorem seqLeft_inv {α β : Type} {p : Parser α} {q : Parser β} {l : List ℕ} {x : α}
    {r : List ℕ} (h : (p <* q) l = some (x, r)) :
    ∃ r1 b, p l = some (x, r1) ∧ q r1 = some (b, r) := by
  simp only [seqLeft_apply, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨a, r1⟩, h1, ⟨b, r2⟩, h2, h3⟩ := h
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  exact ⟨r1, b, h1, h2⟩

theorem orElse_inv {α : Type} {p q : Parser α} {l : List ℕ} {x : α} {r : List ℕ}
    (h : Parser.orElse p q l = some (x, r)) :
    p l = some (x, r) ∨ (p l = none ∧ q l = some (x, r)) := by
  rw [orElse_apply] at h
  cases hp : p l with
  | none => rw [hp] at h; exact Or.inr ⟨rfl, h⟩
  | some ar => rw [hp] at h; exact Or.inl h

/-! ## Hex digits -/

theorem isHex_eq (c : ℕ) : Model.isHex c = isHexDigit c := rfl

theorem hex4_inv {l : List ℕ} {v : ℕ} {r : List ℕ} (h : hex4 l = some (v, r)) :
    ∃ a b c d, Model.isHex a = true ∧ Model.isHex b = true ∧ Model.isHex c = true ∧
      Model.isHex d = true ∧ l = a :: b :: c :: d :: r := by
  rw [hex4] at h
  obtain ⟨a, r1, h1, h⟩ := bind_inv h
  obtain ⟨b, r2, h2, h⟩ := bind_inv h
  obtain ⟨c, r3, h3, h⟩ := bind_inv h
  obtain ⟨d, r4, h4, h⟩ := bind_inv h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hl1, hq1⟩ := satisfy_inv h1
  obtain ⟨hl2, hq2⟩ := satisfy_inv h2
  obtain ⟨hl3, hq3⟩ := satisfy_inv h3
  obtain ⟨hl4, hq4⟩ := satisfy_inv h4
  exact ⟨a, b, c, d, by rw [isHex_eq]; exact hq1, by rw [isHex_eq]; exact hq2,
    by rw [isHex_eq]; exact hq3, by rw [isHex_eq]; exact hq4,
    by rw [hl1, hl2, hl3, hl4, ← h.2]⟩

/-! ## The escapes -/

theorem lowEsc_inv {l : List ℕ} {v : ℕ} {r : List ℕ} (h : lowEsc l = some (v, r)) :
    ∃ a b c d, Model.isHex a = true ∧ Model.isHex b = true ∧ Model.isHex c = true ∧
      Model.isHex d = true ∧ isLowSurrogate (hexNum a b c d) = true ∧
      l = backslash :: lowerU :: a :: b :: c :: d :: r := by
  rw [lowEsc] at h
  obtain ⟨u1, r1, h1, h⟩ := bind_inv h
  obtain ⟨u2, r2, h2, h⟩ := bind_inv h
  obtain ⟨hv, r3, h3, h⟩ := bind_inv h
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hl3⟩ := hex4_inv h3
  have hval : hv = hexNum a b c d := by
    have := hex4_eq ha hb hc hd r3
    rw [← hl3, h3] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1
  subst hval
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    refine ⟨a, b, c, d, ha, hb, hc, hd, by next hs => exact hs, ?_⟩
    rw [byte_inv h1, byte_inv h2, hl3, h.2]
  · simp at h

theorem escape_notSimple {b : ℕ} (h : Model.isSimpleEsc b = false) (t : List ℕ) :
    escape (b :: t) = unicodeEscape (b :: t) := by
  have hne : ∀ c : ℕ, Model.isSimpleEsc c = true → ¬ (b = c) := by
    intro c hc hx
    rw [hx, hc] at h
    exact Bool.noConfusion h
  simp only [escape, alt_apply, orElse_apply, seqRight_apply, byte_cons,
    if_neg (hne quote (by decide)), if_neg (hne backslash (by decide)),
    if_neg (hne slash (by decide)), if_neg (hne lowerB (by decide)),
    if_neg (hne lowerF (by decide)), if_neg (hne lowerN (by decide)),
    if_neg (hne lowerR (by decide)), if_neg (hne lowerT (by decide)),
    Option.bind_none]

theorem unicodeEscape_inv {l : List ℕ} {v : ℕ} {r : List ℕ} (h : unicodeEscape l = some (v, r)) :
    (∃ a b c d, Model.isHex a = true ∧ Model.isHex b = true ∧ Model.isHex c = true ∧
        Model.isHex d = true ∧ l = lowerU :: a :: b :: c :: d :: r ∧
        (isHighSurrogate (hexNum a b c d) = true → NoLow r)) ∨
    (∃ a b c d a' b' c' d', Model.isHex a = true ∧ Model.isHex b = true ∧
        Model.isHex c = true ∧ Model.isHex d = true ∧ Model.isHex a' = true ∧
        Model.isHex b' = true ∧ Model.isHex c' = true ∧ Model.isHex d' = true ∧
        isHighSurrogate (hexNum a b c d) = true ∧ isLowSurrogate (hexNum a' b' c' d') = true ∧
        l = lowerU :: a :: b :: c :: d :: backslash :: lowerU :: a' :: b' :: c' :: d' :: r) := by
  rw [unicodeEscape_eq] at h
  obtain ⟨u1, r1, hbu, hA⟩ := bind_inv h
  obtain ⟨hv, r2, hhex, hB⟩ := bind_inv hA
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hl2⟩ := hex4_inv hhex
  have hval : hv = hexNum a b c d := by
    have hfw := hex4_eq ha hb hc hd r2
    rw [← hl2, hhex] at hfw
    simp only [Option.some.injEq, Prod.mk.injEq] at hfw
    exact hfw.1
  subst hval
  have hb1 := byte_inv hbu
  split at hB
  · next hhigh =>
    obtain ⟨lo, r3, hopt, hC⟩ := bind_inv hB
    rcases optional_inv hopt with ⟨lov, hlo, hlow⟩ | ⟨hlo, hr3, hnone⟩
    · subst hlo
      obtain ⟨a', b', c', d', ha', hb', hc', hd', hlo', hl3⟩ := lowEsc_inv hlow
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hC
      exact Or.inr ⟨a, b, c, d, a', b', c', d', ha, hb, hc, hd, ha', hb', hc', hd',
        hhigh, hlo', by rw [hb1, hl2, hl3, hC.2]⟩
    · subst hlo
      subst hr3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hC
      exact Or.inl ⟨a, b, c, d, ha, hb, hc, hd, by rw [hb1, hl2, hC.2],
        fun _ => by rw [← hC.2]; exact hnone⟩
  · next hhigh =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hB
    exact Or.inl ⟨a, b, c, d, ha, hb, hc, hd, by rw [hb1, hl2, hB.2],
      fun hx => absurd hx (by simpa using hhigh)⟩

theorem escape_inv {l : List ℕ} {v : ℕ} {r : List ℕ} (h : escape l = some (v, r)) :
    (∃ b, Model.isSimpleEsc b = true ∧ l = b :: r) ∨
    (∃ t, l = lowerU :: t ∧ unicodeEscape l = some (v, r)) := by
  cases l with
  | nil =>
    exact absurd h (by rw [show escape ([] : List ℕ) = none from rfl]; simp)
  | cons b t =>
    by_cases hs : Model.isSimpleEsc b = true
    · refine Or.inl ⟨b, hs, ?_⟩
      have hf := stringElem_esc hs t
      have hsat : satisfy Specs.JSON.isUnescaped (backslash :: b :: t) = none := by
        simp [unesc_backslash]
      rw [stringElem, alt_apply, orElse_apply_of_none hsat, seqRight_apply, byte_cons_self,
        Option.bind_some] at hf
      rw [hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [h.2]
    · simp only [Bool.not_eq_true] at hs
      rw [escape_notSimple hs t] at h
      refine Or.inr ⟨t, ?_, h⟩
      rcases unicodeEscape_inv h with ⟨a, b', c, d, -, -, -, -, hl, -⟩ | ⟨a, b', c, d, _, _, _, _,
        -, -, -, -, -, -, -, -, -, -, hl⟩ <;>
        · rw [List.cons.injEq] at hl; rw [hl.1]


/-! ## One string-body element -/

/-- The first element of a body, if any, is not a low surrogate. -/
def HeadNotLow (X : List SE) : Prop := ∀ e rest, X = e :: rest → e.isLow = false

theorem headNotLow_nil : HeadNotLow [] := by intro e rest h; simp at h

theorem specCps_cons_of {e : SE} {L : List SE} (h : e.isHigh = false ∨ HeadNotLow L) :
    specCps (e :: L) = e.scp :: specCps L := by
  cases L with
  | nil => rfl
  | cons e' L' =>
    have hcond : (e.isHigh && e'.isLow) = false := by
      rcases h with h | h
      · rw [h]; rfl
      · rw [h e' L' rfl]; exact Bool.and_false _
    rw [specCps_cons2, if_neg (by simp [hcond])]

theorem isUnescaped_model_of_spec {b : ℕ} (h : Specs.JSON.isUnescaped b = true) (hb : b < 0x80) :
    Model.isUnescaped b = true := by
  simp only [Specs.JSON.isUnescaped, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  simp only [Model.isUnescaped, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨⟨⟨h.1.1, by omega⟩, h.1.2⟩, h.2⟩

set_option maxHeartbeats 1000000 in
theorem stringElem_inv {l : List ℕ} {c : ℕ} {r : List ℕ} (hv : ∀ x ∈ l, ValidCp x)
    (h : stringElem l = some (c, r)) :
    (∃ e : SE, e.WF ∧ l = e.dcps ++ r ∧ c = e.scp ∧ (e.isHigh = true → NoLow r)) ∨
    (∃ e e' : SE, e.WF ∧ e'.WF ∧ e.isHigh = true ∧ e'.isLow = true ∧
      l = e.dcps ++ (e'.dcps ++ r) ∧
      c = 0x10000 + (e.scp - 0xD800) * 0x400 + (e'.scp - 0xDC00)) := by
  cases hsat : satisfy Specs.JSON.isUnescaped l with
  | some ar =>
    obtain ⟨cc, rr⟩ := ar
    rw [stringElem, alt_apply, orElse_apply_of_some hsat] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hl, hq⟩ := satisfy_inv hsat
    obtain ⟨rfl, rfl⟩ := h
    by_cases hasc : cc < 0x80
    · refine Or.inl ⟨.plain cc, isUnescaped_model_of_spec hq hasc, ?_, rfl, ?_⟩
      · rw [hl]; rfl
      · intro hx; exact absurd hx (by simp [SE.isHigh])
    · have hval : ValidCp cc := hv cc (by rw [hl]; exact List.mem_cons_self ..)
      refine Or.inl ⟨seOfCp cc, seOfCp_WF (by omega) hval, ?_, (seOfCp_scp (by omega)).symm, ?_⟩
      · rw [hl, seOfCp_dcps (by omega)]; rfl
      · intro hx; rw [seOfCp_isHigh] at hx; exact Bool.noConfusion hx
  | none =>
    have hse := h
    rw [stringElem, alt_apply, orElse_apply_of_none hsat] at hse
    obtain ⟨u1, l1, hby, hesc⟩ := seqRight_inv hse
    have hlb : l = backslash :: l1 := byte_inv hby
    rcases escape_inv hesc with ⟨b, hsimple, hl1⟩ | ⟨t, hl1, huni⟩
    · have hfw := stringElem_esc hsimple r
      rw [← hl1, ← hlb] at hfw
      rw [hfw] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨.esc b, hsimple, by rw [hlb, hl1]; rfl, h.1.symm,
        fun hx => absurd hx (by simp [SE.isHigh])⟩
    · rcases unicodeEscape_inv huni with
        ⟨a, b, c', d, ha, hb, hc, hd, hl2, hnl⟩ |
        ⟨a, b, c', d, a', b', c'', d', ha, hb, hc, hd, ha', hb', hc', hd', hhi, hlo, hl2⟩
      · have hshape : l = backslash :: lowerU :: a :: b :: c' :: d :: r := by rw [hlb, hl2]
        have hcond : isHighSurrogate (hexNum a b c' d) = false ∨ NoLow r := by
          by_cases hh : isHighSurrogate (hexNum a b c' d) = true
          · exact Or.inr (hnl hh)
          · exact Or.inl (by simpa using hh)
        have hfw := stringElem_hex ha hb hc hd r hcond
        rw [← hshape] at hfw
        rw [hfw] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inl ⟨.hex a b c' d, ⟨ha, hb, hc, hd⟩, by rw [hshape]; rfl, h.1.symm,
          fun hx => hnl hx⟩
      · have hshape : l = backslash :: lowerU :: a :: b :: c' :: d ::
            backslash :: lowerU :: a' :: b' :: c'' :: d' :: r := by rw [hlb, hl2]
        have hfw := stringElem_pair ha hb hc hd ha' hb' hc' hd' hhi hlo r
        rw [← hshape] at hfw
        rw [hfw] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inr ⟨.hex a b c' d, .hex a' b' c'' d', ⟨ha, hb, hc, hd⟩,
          ⟨ha', hb', hc', hd'⟩, hhi, hlo, by rw [hshape]; rfl, h.1.symm⟩


/-! ## A whole string body -/

theorem headNotLow_append {A B : List SE} (hA : HeadNotLow A) (hB : HeadNotLow B) :
    HeadNotLow (A ++ B) := by
  intro e rest hab
  cases A with
  | nil => exact hB e rest (by simpa using hab)
  | cons x A' =>
    rw [List.cons_append, List.cons.injEq] at hab
    rw [← hab.1]
    exact hA x A' rfl

theorem headNotLow_of_noLow {body : List SE} {l r : List ℕ} (hwf : ∀ e ∈ body, e.WF)
    (hl : l = dcpsList body ++ r) (hno : NoLow l) : HeadNotLow body := by
  intro e rest hb
  by_contra hlow
  simp only [Bool.not_eq_false] at hlow
  obtain ⟨a, b, c, d, rfl⟩ := isLow_hex hlow
  have hx : Model.isHex a = true ∧ Model.isHex b = true ∧ Model.isHex c = true ∧
      Model.isHex d = true := hwf _ (by rw [hb]; exact List.mem_cons_self ..)
  have hlo : isLowSurrogate (hexNum a b c d) = true := hlow
  have hshape : l = backslash :: lowerU :: a :: b :: c :: d :: (dcpsList rest ++ r) := by
    rw [hl, hb, dcpsList_cons]
    rfl
  have := lowEsc_pair hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 hlo (dcpsList rest ++ r)
  rw [← hshape, hno] at this
  exact absurd this (by simp)

theorem chain_stringElem {l : List ℕ} {cs : List ℕ} {r : List ℕ}
    (hch : Chain stringElem l cs r) : (∀ x ∈ l, ValidCp x) →
    ∃ body : List SE, (∀ e ∈ body, e.WF) ∧ l = dcpsList body ++ r ∧
      (∀ X : List SE, HeadNotLow X → specCps (body ++ X) = cs ++ specCps X) := by
  induction hch with
  | nil r =>
    intro _
    exact ⟨[], by simp, by simp, fun X _ => by simp⟩
  | @cons l a r1 as r hstep hrest ih =>
    intro hv
    rcases stringElem_inv hv hstep with ⟨e, hwf, hl, hval, hhi⟩ |
      ⟨e, e', hwf, hwf', hhigh, hlow, hl, hval⟩
    · have hv1 : ∀ x ∈ r1, ValidCp x := by
        intro x hx; exact hv x (by rw [hl]; exact List.mem_append_right _ hx)
      obtain ⟨body', hwf', hl', hsp'⟩ := ih hv1
      refine ⟨e :: body', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hwf
        · exact hwf' x hx
      · rw [hl, hl', dcpsList_cons, List.append_assoc]
      · intro X hX
        have hcond : e.isHigh = false ∨ HeadNotLow (body' ++ X) := by
          by_cases hh : e.isHigh = true
          · exact Or.inr (headNotLow_append
              (headNotLow_of_noLow hwf' hl' (hhi hh)) hX)
          · exact Or.inl (by simpa using hh)
        rw [List.cons_append, specCps_cons_of hcond, hsp' X hX, hval]
        rfl
    · have hv1 : ∀ x ∈ r1, ValidCp x := by
        intro x hx
        exact hv x (by rw [hl]; exact List.mem_append_right _ (List.mem_append_right _ hx))
      obtain ⟨body', hwfb, hl', hsp'⟩ := ih hv1
      refine ⟨e :: e' :: body', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hwf
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hwf'
          · exact hwfb x hx
      · rw [hl, hl', dcpsList_cons, dcpsList_cons, List.append_assoc, List.append_assoc]
      · intro X hX
        rw [List.cons_append, List.cons_append, specCps_cons2,
          if_pos (by simp [hhigh, hlow]), hsp' X hX, hval]
        rfl

theorem string_inv {l : List ℕ} {sv : List ℕ} {r : List ℕ} (hv : ∀ x ∈ l, ValidCp x)
    (h : Specs.JSON.string l = some (sv, r)) :
    ∃ body : List SE, (∀ e ∈ body, e.WF) ∧ l = quote :: (dcpsList body ++ (quote :: r)) ∧
      specCps body = sv := by
  rw [Specs.JSON.string] at h
  obtain ⟨r1, ub, hmany, hq2⟩ := seqLeft_inv h
  obtain ⟨u1, l1, hq1, hmany'⟩ := seqRight_inv hmany
  have hlq : l = quote :: l1 := byte_inv hq1
  have hr1 : r1 = quote :: r := byte_inv hq2
  have hv1 : ∀ x ∈ l1, ValidCp x := by
    intro x hx; exact hv x (by rw [hlq]; exact List.mem_cons_of_mem _ hx)
  rw [hr1] at hmany'
  obtain ⟨body, hwf, hl1, hsp⟩ := chain_stringElem (many_chain hmany') hv1
  refine ⟨body, hwf, by rw [hlq, hl1], ?_⟩
  have := hsp [] headNotLow_nil
  rw [List.append_nil, specCps_nil, List.append_nil] at this
  exact this


/-! ## Digit runs -/

theorem digitsOf_cons (x : ℕ) (l : List ℕ) : digitsOf (x :: l) = (x + digit0) :: digitsOf l := by
  simp [digitsOf]

theorem digitValue_le_9 {c : ℕ} (h : Specs.JSON.isDigit c = true) : digitValue c ≤ 9 := by
  simp only [Specs.JSON.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : (0x30 : ℕ) ≤ c := h.1
  have h2 : c ≤ 0x39 := h.2
  show c - 0x30 ≤ 9
  omega

theorem digitsOf_digitValue : ∀ {cs : List ℕ}, (∀ x ∈ cs, Specs.JSON.isDigit x = true) →
    digitsOf (cs.map digitValue) = cs := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c t ih =>
    intro h
    have hc := h c (List.mem_cons_self ..)
    simp only [Specs.JSON.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 : (0x30 : ℕ) ≤ c := hc.1
    rw [List.map_cons, digitsOf_cons, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    congr 1
    show c - 0x30 + 0x30 = c
    omega

theorem digits1_inv {l : List ℕ} {ds : List ℕ} {r : List ℕ} (h : digits1 l = some (ds, r)) :
    ds ≠ [] ∧ (∀ x ∈ ds, x ≤ 9) ∧ l = digitsOf ds ++ r := by
  rw [digits1] at h
  obtain ⟨d, t, hd, hA⟩ := bind_inv h
  obtain ⟨ds', r', hmany, hB⟩ := bind_inv hA
  obtain ⟨hl, hq⟩ := satisfy_inv hd
  rw [many_satisfy] at hmany
  simp only [Option.some.injEq, Prod.mk.injEq] at hmany
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hB
  obtain ⟨hds, hrr⟩ := hB
  have hall : ∀ x ∈ (d :: ds'), Specs.JSON.isDigit x = true := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hq
    · rw [← hmany.1] at hx; exact takeWhile_mem x hx
  refine ⟨?_, ?_, ?_⟩
  · rw [← hds]; simp
  · intro x hx
    rw [← hds, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact digitValue_le_9 (hall y hy)
  · rw [← hds, digitsOf_digitValue hall, hl, ← hrr, ← hmany.2, ← hmany.1, List.cons_append,
      List.takeWhile_append_dropWhile]

theorem intDigits_inv {l : List ℕ} {ints : List ℕ} {r : List ℕ}
    (h : intDigits l = some (ints, r)) :
    (ints = [0] ∨ (∃ d ds, ints = d :: ds ∧ 1 ≤ d ∧ d ≤ 9 ∧ ∀ x ∈ ds, x ≤ 9)) ∧
      l = digitsOf ints ++ r := by
  rw [intDigits, alt_apply] at h
  rcases orElse_inv h with hz | ⟨-, hz⟩
  · obtain ⟨u1, l1, hpre, hA⟩ := seqRight_inv hz
    obtain ⟨u2, l2, hb0, hnf⟩ := seqRight_inv hpre
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hA
    have hl2 : l = digit0 :: l2 := byte_inv hb0
    have hl1 : l1 = l2 := by
      cases l2 with
      | nil =>
        simp only [notFollowedBy_nil, Option.some.injEq, Prod.mk.injEq] at hnf
        exact hnf.2.symm
      | cons c t =>
        rw [notFollowedBy_cons] at hnf
        split at hnf
        · simp at hnf
        · simp only [Option.some.injEq, Prod.mk.injEq] at hnf; exact hnf.2.symm
    refine ⟨Or.inl ?_, ?_⟩
    · rw [← hA.1]
    · rw [← hA.1, ← hA.2, hl1, hl2]
      simp [digitsOf]
  · obtain ⟨d, t, hd, hA⟩ := bind_inv hz
    obtain ⟨ds', r', hmany, hB⟩ := bind_inv hA
    obtain ⟨hl, hq⟩ := satisfy_inv hd
    rw [many_satisfy] at hmany
    simp only [Option.some.injEq, Prod.mk.injEq] at hmany
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hB
    obtain ⟨hds, hrr⟩ := hB
    simp only [Specs.JSON.isDigitNz, Bool.and_eq_true, decide_eq_true_eq] at hq
    have hqd : Specs.JSON.isDigit d = true := by
      simp only [Specs.JSON.isDigit, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hall : ∀ x ∈ (d :: ds'), Specs.JSON.isDigit x = true := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hqd
      · rw [← hmany.1] at hx; exact takeWhile_mem x hx
    refine ⟨Or.inr ⟨digitValue d, ds'.map digitValue, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [← hds]; rfl
    · simp only [digitValue]; omega
    · exact digitValue_le_9 hqd
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact digitValue_le_9 (hall y (List.mem_cons_of_mem _ hy))
    · rw [← hds, digitsOf_digitValue hall, hl, ← hrr, ← hmany.2, ← hmany.1, List.cons_append,
        List.takeWhile_append_dropWhile]


/-! ## Numbers -/

theorem exponent_inv {l : List ℕ} {b : Bool} {ds : List ℕ} {r : List ℕ}
    (h : exponent l = some ((b, ds), r)) :
    ∃ e : SExp, (e.letter = lowerE ∨ e.letter = upperE) ∧
      (match e.sign with | none => True | some sg => sg = plus ∨ sg = minus) ∧
      e.digits ≠ [] ∧ (∀ x ∈ e.digits, x ≤ 9) ∧ e.digits = ds ∧
      b = decide (e.sign = some minus) ∧ l = SExp.bytes e ++ r := by
  rw [exponent] at h
  obtain ⟨u1, l1, hlet, hA⟩ := bind_inv h
  obtain ⟨neg, l2, hsign, hB⟩ := bind_inv hA
  obtain ⟨dsv, l3, hdig, hC⟩ := bind_inv hB
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hC
  obtain ⟨⟨hnegb, hdseq⟩, hbb⟩ := hC
  obtain ⟨hdne, hd9, hl2⟩ := digits1_inv hdig
  rw [alt_apply] at hlet
  have hletter : (l = lowerE :: l1 ∧ lowerE = lowerE) ∨ (l = upperE :: l1) := by
    rcases orElse_inv hlet with hx | ⟨-, hx⟩
    · exact Or.inl ⟨byte_inv hx, rfl⟩
    · exact Or.inr (byte_inv hx)
  have hlt : ∃ lt, (lt = lowerE ∨ lt = upperE) ∧ l = lt :: l1 := by
    rcases hletter with ⟨hx, -⟩ | hx
    · exact ⟨lowerE, Or.inl rfl, hx⟩
    · exact ⟨upperE, Or.inr rfl, hx⟩
  obtain ⟨lt, hltv, hll⟩ := hlt
  rw [alt_apply] at hsign
  have hsg : ∃ sg : Option ℕ, (match sg with | none => True | some s => s = plus ∨ s = minus) ∧
      neg = decide (sg = some minus) ∧
      l1 = (match sg with | none => [] | some s => [s]) ++ l2 := by
    rcases orElse_inv hsign with hx | ⟨-, hx⟩
    · obtain ⟨u, l', hb, hp⟩ := seqRight_inv hx
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hp
      exact ⟨some plus, Or.inl rfl, by rw [← hp.1]; decide, by rw [byte_inv hb, hp.2]; rfl⟩
    · rw [alt_apply] at hx
      rcases orElse_inv hx with hy | ⟨-, hy⟩
      · obtain ⟨u, l', hb, hp⟩ := seqRight_inv hy
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hp
        exact ⟨some minus, Or.inr rfl, by rw [← hp.1]; decide, by rw [byte_inv hb, hp.2]; rfl⟩
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hy
        exact ⟨none, trivial, by rw [← hy.1]; decide, by rw [hy.2]; rfl⟩
  obtain ⟨sg, hsgok, hnegv, hl1⟩ := hsg
  refine ⟨⟨lt, sg, dsv⟩, hltv, hsgok, hdne, hd9, hdseq, ?_, ?_⟩
  · rw [← hnegb, hnegv]
  · rw [hll, hl1, hl2, ← hbb, SExp.bytes]
    simp only [List.cons_append, List.append_assoc]
    rfl

set_option maxHeartbeats 1000000 in
theorem number_inv {l : List ℕ} {jn : JNumber} {r : List ℕ} (h : number l = some (jn, r)) :
    ∃ nm : SNum, nm.WF ∧ l = nm.bytes ++ r ∧ jnumOf nm = jn := by
  rw [number] at h
  obtain ⟨negOpt, l1, hneg, hA⟩ := bind_inv h
  obtain ⟨ints, l2, hint, hB⟩ := bind_inv hA
  obtain ⟨fracOpt, l3, hfrac, hC⟩ := bind_inv hB
  obtain ⟨expOpt, l4, hexp, hD⟩ := bind_inv hC
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hD
  obtain ⟨hrec, hl4⟩ := hD
  -- the sign
  have hsign : l = (if negOpt.isSome then [minus] else []) ++ l1 := by
    rcases optional_inv hneg with ⟨u, hu, hb⟩ | ⟨hu, hl1, -⟩
    · rw [hu]; simpa using byte_inv hb
    · rw [hu]; simpa using hl1.symm
  -- the integer part
  obtain ⟨hintwf, hl1⟩ := intDigits_inv hint
  -- the fractional part
  have hfr : ∃ fl : List ℕ, (∀ x ∈ fl, x ≤ 9) ∧ fl = fracOpt.getD [] ∧
      l2 = (if fl = [] then [] else dot :: digitsOf fl) ++ l3 := by
    rcases optional_inv hfrac with ⟨ds, hu, hs⟩ | ⟨hu, hl3, -⟩
    · obtain ⟨u, l2', hb, hdig⟩ := seqRight_inv hs
      obtain ⟨hne, h9, hl2'⟩ := digits1_inv hdig
      exact ⟨ds, h9, by rw [hu]; rfl, by rw [byte_inv hb, hl2', if_neg hne]; rfl⟩
    · exact ⟨[], by simp, by rw [hu]; rfl, by rw [hl3]; simp⟩
  obtain ⟨fl, hfl9, hflv, hl2⟩ := hfr
  -- the exponent
  have hex : ∃ ex : Option SExp, (match ex with
        | none => True
        | some e => (e.letter = lowerE ∨ e.letter = upperE) ∧
            (match e.sign with | none => True | some sg => sg = plus ∨ sg = minus) ∧
            e.digits ≠ [] ∧ ∀ x ∈ e.digits, x ≤ 9) ∧
      (ex.map fun e => decide (e.sign = some minus)) = expOpt.map (·.1) ∧
      (ex.map (·.digits)) = expOpt.map (·.2) ∧
      l3 = (ex.map SExp.bytes).getD [] ++ l4 := by
    rcases optional_inv hexp with ⟨pr, hu, hs⟩ | ⟨hu, hl4', -⟩
    · obtain ⟨bb, dss⟩ := pr
      obtain ⟨e, hlt, hsg, hne, h9, hdeq, hbv, hl3⟩ := exponent_inv hs
      exact ⟨some e, ⟨hlt, hsg, hne, h9⟩, by rw [hu]; simp [← hbv],
        by rw [hu]; simp [hdeq], by rw [hl3]; rfl⟩
    · exact ⟨none, trivial, by rw [hu]; rfl, by rw [hu]; rfl, by rw [hl4']; rfl⟩
  obtain ⟨ex, hexwf, hexneg, hexdig, hl3⟩ := hex
  refine ⟨⟨negOpt.isSome, ints, fl, ex⟩, ⟨hintwf, hfl9, ?_⟩, ?_, ?_⟩
  · cases ex with
    | none => exact trivial
    | some e => exact ⟨hexwf.1, hexwf.2.1, hexwf.2.2.1, hexwf.2.2.2⟩
  · rw [snum_bytes_eq]
    dsimp only [fracPart, expPart]
    rw [hsign, hl1, hl2, hl3, hl4]
    simp only [List.append_assoc]
  · simp only [jnumOf, hflv, hexneg, hexdig]
    exact hrec


/-! ## Values -/

theorem map_inv {α β : Type} {f : α → β} {p : Parser α} {l : List ℕ} {x : β} {r : List ℕ}
    (h : (f <$> p) l = some (x, r)) : ∃ a, p l = some (a, r) ∧ x = f a := by
  simp only [map_apply, Option.map_eq_some_iff] at h
  obtain ⟨⟨a, r'⟩, h1, h2⟩ := h
  simp only [Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  exact ⟨a, h1, rfl⟩

set_option maxHeartbeats 1000000 in
theorem value_inv {f : ℕ} {l : List ℕ} {j : JSON} {r : List ℕ}
    (h : value (f + 1) l = some (j, r)) :
    ∃ w l1, IsWs w ∧ l = w ++ l1 ∧
      ((∃ ms, j = .obj ms ∧ object f l1 = some (ms, r)) ∨
       (∃ es, j = .arr es) ∨
       (∃ sv, j = .str sv ∧ Specs.JSON.string l1 = some (sv, r)) ∨
       (j = .bool true ∧ l1 = trueLit ++ r) ∨
       (j = .bool false ∧ l1 = falseLit ++ r) ∨
       (j = .null ∧ l1 = nullLit ++ r) ∨
       (∃ n, j = .num n ∧ number l1 = some (n, r))) := by
  rw [value] at h
  obtain ⟨u, l1, hws, hbr⟩ := seqRight_inv h
  obtain ⟨w, hwsw, hlw, -⟩ := ws_inv hws
  refine ⟨w, l1, hwsw, hlw, ?_⟩
  simp only [alt_apply] at hbr
  rcases orElse_inv hbr with hx | ⟨-, hbr⟩
  · obtain ⟨ms, hms, hj⟩ := map_inv hx
    exact Or.inl ⟨ms, hj, hms⟩
  rcases orElse_inv hbr with hx | ⟨-, hbr⟩
  · obtain ⟨es, -, hj⟩ := map_inv hx
    exact Or.inr (Or.inl ⟨es, hj⟩)
  rcases orElse_inv hbr with hx | ⟨-, hbr⟩
  · obtain ⟨sv, hsv, hj⟩ := map_inv hx
    exact Or.inr (Or.inr (Or.inl ⟨sv, hj, hsv⟩))
  rcases orElse_inv hbr with hx | ⟨-, hbr⟩
  · obtain ⟨u2, l2, hlit, hp⟩ := seqRight_inv hx
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hp
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp.1.symm, by rw [← hp.2]; exact literal_inv _ hlit⟩)))
  rcases orElse_inv hbr with hx | ⟨-, hbr⟩
  · obtain ⟨u2, l2, hlit, hp⟩ := seqRight_inv hx
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hp
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hp.1.symm, by rw [← hp.2]; exact literal_inv _ hlit⟩))))
  rcases orElse_inv hbr with hx | ⟨-, hbr⟩
  · obtain ⟨u2, l2, hlit, hp⟩ := seqRight_inv hx
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hp
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hp.1.symm, by rw [← hp.2]; exact literal_inv _ hlit⟩)))))
  · obtain ⟨n, hn, hj⟩ := map_inv hbr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hj, hn⟩)))))

theorem value_inv_sv {f : ℕ} {l : List ℕ} {j : JSON} {r : List ℕ} (hv : ∀ x ∈ l, ValidCp x)
    (h : value f l = some (j, r)) (hsc : Specs.JSONSchema.IsScalar j) :
    ∃ (w : List ℕ) (v : SV), IsWs w ∧ v.WF ∧ v.json = j ∧ l = w ++ (SV.cps v ++ r) := by
  cases f with
  | zero => rw [value] at h; simp [fail] at h
  | succ f =>
    obtain ⟨w, l1, hwsw, hlw, hcases⟩ := value_inv h
    have hv1 : ∀ x ∈ l1, ValidCp x := by
      intro x hx; exact hv x (by rw [hlw]; exact List.mem_append_right _ hx)
    rcases hcases with ⟨ms, hj, -⟩ | ⟨es, hj⟩ | ⟨sv, hj, hstr⟩ | ⟨hj, hl1⟩ | ⟨hj, hl1⟩ |
      ⟨hj, hl1⟩ | ⟨n, hj, hnum⟩
    · rw [hj] at hsc; exact absurd hsc (by simp [Specs.JSONSchema.IsScalar])
    · rw [hj] at hsc; exact absurd hsc (by simp [Specs.JSONSchema.IsScalar])
    · obtain ⟨body, hwf, hl1, hsp⟩ := string_inv hv1 hstr
      refine ⟨w, .str body, hwsw, hwf, by rw [hj, SV.json, hsp], ?_⟩
      rw [hlw, hl1]
      simp only [SV.cps, List.append_assoc, List.cons_append, List.nil_append]
    · exact ⟨w, .btrue, hwsw, trivial, hj.symm, by rw [hlw, hl1]; rfl⟩
    · exact ⟨w, .bfalse, hwsw, trivial, hj.symm, by rw [hlw, hl1]; rfl⟩
    · exact ⟨w, .null, hwsw, trivial, hj.symm, by rw [hlw, hl1]; rfl⟩
    · obtain ⟨nm, hwf, hl1, hjn⟩ := number_inv hnum
      exact ⟨w, .num nm, hwsw, hwf, by rw [hj, SV.json, ← hjn]; rfl, by rw [hlw, hl1]; rfl⟩

/-! ## Members -/

/-- Everything `SMem.WF` asks for except the claim-dependent value condition. -/
def MemStruct (m : SMem) : Prop :=
  IsWs m.ws0 ∧ IsWs m.ws1 ∧ IsWs m.ws2 ∧ IsWs m.ws3 ∧ (∀ e ∈ m.key, e.WF) ∧ m.val.WF

theorem member_inv {f : ℕ} {l : List ℕ} {k : List ℕ} {v : JSON} {r : List ℕ}
    (hv : ∀ x ∈ l, ValidCp x) (h : member f l = some ((k, v), r))
    (hsc : Specs.JSONSchema.IsScalar v) {w3 rr : List ℕ} (hw3 : IsWs w3) (hr : r = w3 ++ rr) :
    ∃ m : SMem, MemStruct m ∧ m.skey = k ∧ m.val.json = v ∧ m.ws3 = w3 ∧
      l = SMem.cps m ++ rr := by
  rw [member] at h
  obtain ⟨u0, l1, hws0, hA⟩ := bind_inv h
  obtain ⟨key, l2, hstr, hB⟩ := bind_inv hA
  obtain ⟨u1, l3, hws1, hC⟩ := bind_inv hB
  obtain ⟨u2, l4, hcol, hD⟩ := bind_inv hC
  obtain ⟨vv, l5, hval, hE⟩ := bind_inv hD
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hE
  obtain ⟨⟨hk, hvv⟩, hl5⟩ := hE
  obtain ⟨w0, hw0, hlw0, -⟩ := ws_inv hws0
  have hv1 : ∀ x ∈ l1, ValidCp x := by
    intro x hx; exact hv x (by rw [hlw0]; exact List.mem_append_right _ hx)
  obtain ⟨body, hbwf, hl1, hsp⟩ := string_inv hv1 hstr
  obtain ⟨w1, hw1, hlw1, -⟩ := ws_inv hws1
  have hl3 : l3 = colon :: l4 := byte_inv hcol
  have hv4 : ∀ x ∈ l4, ValidCp x := by
    intro x hx
    refine hv x ?_
    rw [hlw0, hl1]
    refine List.mem_append_right _ ?_
    refine List.mem_cons_of_mem _ ?_
    refine List.mem_append_right _ ?_
    refine List.mem_cons_of_mem _ ?_
    rw [hlw1, hl3]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
  have hscv : Specs.JSONSchema.IsScalar vv := by rw [hvv]; exact hsc
  obtain ⟨w2, sv, hw2, hsvwf, hsvj, hl4⟩ := value_inv_sv hv4 hval hscv
  refine ⟨⟨w0, body, w1, w2, sv, w3⟩, ⟨hw0, hw1, hw2, hw3, hbwf, hsvwf⟩, ?_, ?_, rfl, ?_⟩
  · show specCps body = k; rw [hsp, hk]
  · show SV.json sv = v; rw [hsvj, hvv]
  · show l = (w0 ++ [quote] ++ dcpsList body ++ [quote] ++ w1 ++ [colon] ++ w2 ++ SV.cps sv)
      ++ w3 ++ rr
    rw [hlw0, hl1, hlw1, hl3, hl4, hl5, hr]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]


/-! ## The member list -/

theorem isWs_nil : IsWs [] := by intro x hx; simp at hx

theorem isWs_append {a b : List ℕ} (ha : IsWs a) (hb : IsWs b) : IsWs (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

/-- Put the whitespace that follows a member's value into its `ws3` field. -/
def setWs3 (m : SMem) (w : List ℕ) : SMem := { m with ws3 := w }

theorem cps_setWs3 {m : SMem} (h : m.ws3 = []) (w : List ℕ) :
    SMem.cps (setWs3 m w) = SMem.cps m ++ w := by
  simp only [SMem.cps, SMem.cpsNoWs3, setWs3, h, List.append_nil]

theorem memStruct_setWs3 {m : SMem} (h : MemStruct m) {w : List ℕ} (hw : IsWs w) :
    MemStruct (setWs3 m w) := ⟨h.1, h.2.1, h.2.2.1, hw, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem skey_setWs3 (m : SMem) (w : List ℕ) : (setWs3 m w).skey = m.skey := rfl
theorem val_setWs3 (m : SMem) (w : List ℕ) : (setWs3 m w).val = m.val := rfl

theorem chain_members {f : ℕ} : ∀ {l : List ℕ} {as : List (List ℕ × JSON)} {r : List ℕ},
    Chain ((ws *> byte comma) *> member f) l as r → (∀ x ∈ l, ValidCp x) →
    (∀ a ∈ as, Specs.JSONSchema.IsScalar a.2) →
    ∀ {wt rr : List ℕ}, IsWs wt → r = wt ++ rr →
    ∃ (w0 : List ℕ) (ms : List SMem), IsWs w0 ∧ (∀ m ∈ ms, MemStruct m) ∧
      (ms.map fun m => (m.skey, SV.json m.val)) = as ∧
      l = w0 ++ ((ms.map fun m => comma :: SMem.cps m).flatten ++
        ((if as = [] then wt else []) ++ rr)) := by
  intro l as r hch
  induction hch with
  | nil r =>
    intro _ _ wt rr hwt hr
    exact ⟨[], [], isWs_nil, by simp, rfl, by simp [hr]⟩
  | @cons l a r1 as r hstep hrest ih =>
    intro hv hsc wt rr hwt hr
    obtain ⟨u, l', hsep, hmem⟩ := seqRight_inv hstep
    obtain ⟨u', l'', hwsx, hcomma⟩ := seqRight_inv hsep
    obtain ⟨wa, hwa, hlwa, -⟩ := ws_inv hwsx
    have hl'' : l'' = comma :: l' := byte_inv hcomma
    have hvl' : ∀ x ∈ l', ValidCp x := by
      intro x hx
      exact hv x (by rw [hlwa, hl'']; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    obtain ⟨a1, a2⟩ := a
    obtain ⟨m0, hstr0, hskey, hjson, hw30, hl'⟩ :=
      member_inv hvl' hmem (hsc _ (List.mem_cons_self ..)) (w3 := []) (rr := r1) isWs_nil
        (by simp)
    have hvr1 : ∀ x ∈ r1, ValidCp x := by
      intro x hx; exact hvl' x (by rw [hl']; exact List.mem_append_right _ hx)
    obtain ⟨w0', ms', hw0', hms', hmap', hr1⟩ :=
      ih hvr1 (fun x hx => hsc x (List.mem_cons_of_mem _ hx)) hwt hr
    refine ⟨wa, setWs3 m0 (w0' ++ (if as = [] then wt else [])) :: ms', hwa, ?_, ?_, ?_⟩
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact memStruct_setWs3 hstr0 (isWs_append hw0' (by split <;> [exact hwt; exact isWs_nil]))
      · exact hms' m hm
    · rw [List.map_cons, hmap', skey_setWs3, val_setWs3, hskey, hjson]
    · rw [List.map_cons, List.flatten_cons, cps_setWs3 hw30, hlwa, hl'', hl', hr1]
      by_cases has : as = []
      · subst has
        have : ms' = [] := List.map_eq_nil_iff.mp hmap'
        subst this
        simp
      · rw [if_neg has, if_neg (by simp)]
        simp [List.append_assoc]

/-! ## Objects -/

theorem object_inv {f : ℕ} {l : List ℕ} {as : List (List ℕ × JSON)} {r : List ℕ}
    (hv : ∀ x ∈ l, ValidCp x) (h : object f l = some (as, r))
    (hsc : ∀ a ∈ as, Specs.JSONSchema.IsScalar a.2) :
    ∃ (ms : List SMem) (we : List ℕ), IsWs we ∧ (∀ m ∈ ms, MemStruct m) ∧
      (ms.map fun m => (m.skey, SV.json m.val)) = as ∧
      l = lbrace :: (bodyCps ms we ++ (rbrace :: r)) := by
  rw [object] at h
  obtain ⟨r1, ub, hA, hrb⟩ := seqLeft_inv h
  obtain ⟨r2, uw, hB, hwsr⟩ := seqLeft_inv hA
  obtain ⟨u0, l1, hlb, hsep⟩ := seqRight_inv hB
  have hll : l = lbrace :: l1 := byte_inv hlb
  have hr1 : r1 = rbrace :: r := byte_inv hrb
  obtain ⟨w, hw, hr2, -⟩ := ws_inv hwsr
  rw [hr1] at hr2
  have hvl1 : ∀ x ∈ l1, ValidCp x := by
    intro x hx; exact hv x (by rw [hll]; exact List.mem_cons_of_mem _ hx)
  rcases sepBy_inv hsep with ⟨has, hl1⟩ | ⟨a, r1', as', has, hmem, hchain⟩
  · exact ⟨[], w, hw, by simp, by rw [has]; rfl, by rw [hll, ← hl1, hr2]; rfl⟩
  · subst has
    obtain ⟨a1, a2⟩ := a
    obtain ⟨m0, hstr0, hskey, hjson, hw30, hl1⟩ :=
      member_inv hvl1 hmem (hsc _ (List.mem_cons_self ..)) (w3 := []) (rr := r1') isWs_nil
        (by simp)
    have hvr1' : ∀ x ∈ r1', ValidCp x := by
      intro x hx; exact hvl1 x (by rw [hl1]; exact List.mem_append_right _ hx)
    obtain ⟨w0', ms', hw0', hms', hmap', hrr⟩ :=
      chain_members hchain hvr1' (fun x hx => hsc x (List.mem_cons_of_mem _ hx)) hw hr2
    refine ⟨setWs3 m0 (w0' ++ (if as' = [] then w else [])) :: ms', [], isWs_nil, ?_, ?_, ?_⟩
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact memStruct_setWs3 hstr0 (isWs_append hw0' (by split <;> [exact hw; exact isWs_nil]))
      · exact hms' m hm
    · rw [List.map_cons, hmap', skey_setWs3, val_setWs3, hskey, hjson]
    · rw [hll, hl1, hrr, bodyCps, cps_setWs3 hw30]
      by_cases has : as' = []
      · subst has
        have : ms' = [] := List.map_eq_nil_iff.mp hmap'
        subst this
        simp
      · rw [if_neg has]
        simp [List.append_assoc]


/-! ## The whole document -/

/-- `Ser.SWF` without the claim-dependent part of member well-formedness. -/
def SerStruct (sr : Ser) : Prop :=
  IsWs sr.pre ∧ IsWs sr.wsEmpty ∧ IsWs sr.post ∧ ∀ m ∈ sr.body, MemStruct m

theorem document_inv {cps : List ℕ} {ms : List (List ℕ × JSON)} {r : List ℕ}
    (hv : ∀ x ∈ cps, ValidCp x) (h : document cps = some (.obj ms, r))
    (hsc : ∀ a ∈ ms, Specs.JSONSchema.IsScalar a.2) :
    ∃ sr : Ser, SerStruct sr ∧ (sr.body.map fun m => (m.skey, SV.json m.val)) = ms ∧
      cps = Ser.cps sr := by
  rw [document] at h
  obtain ⟨r1, ue, hA, heof⟩ := seqLeft_inv h
  obtain ⟨r2, uw, hval, hwsr⟩ := seqLeft_inv hA
  obtain ⟨post, hpost, hr2, -⟩ := ws_inv hwsr
  obtain ⟨hnil, -⟩ := eof_inv heof
  rw [hnil, List.append_nil] at hr2
  obtain ⟨w, l1, hw, hcps, hcases⟩ := value_inv hval
  have hvl1 : ∀ x ∈ l1, ValidCp x := by
    intro x hx; exact hv x (by rw [hcps]; exact List.mem_append_right _ hx)
  rcases hcases with ⟨ms', hj, hobj⟩ | ⟨es, hj⟩ | ⟨sv, hj, -⟩ | ⟨hj, -⟩ | ⟨hj, -⟩ | ⟨hj, -⟩ |
    ⟨n, hj, -⟩
  · have hms : ms' = ms := by injection hj.symm
    subst hms
    obtain ⟨body, we, hwe, hstr, hmap, hl1⟩ := object_inv hvl1 hobj hsc
    refine ⟨⟨w, body, we, post⟩, ⟨hw, hwe, hpost, hstr⟩, hmap, ?_⟩
    show cps = w ++ [lbrace] ++ bodyCps body we ++ [rbrace] ++ post
    rw [hcps, hl1, hr2]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
  · exact absurd hj.symm (by simp)
  · exact absurd hj.symm (by simp)
  · exact absurd hj.symm (by simp)
  · exact absurd hj.symm (by simp)
  · exact absurd hj.symm (by simp)
  · exact absurd hj.symm (by simp)


end ParseInv

end Solution.JSONExtract
