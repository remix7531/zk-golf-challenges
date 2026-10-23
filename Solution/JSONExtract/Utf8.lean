import Solution.JSONExtract.Serial

/-!
# The UTF-8 layer of the specification (`JSONExtract`)

`Specs.JSON.utf8Decode` is `many codepoint <* eof`.  `Utf8 bs cps` says the
byte list `bs` splits into self-delimiting `codepoint` tokens whose values are
`cps`; it is closed under concatenation, holds for ASCII bytes, and implies
`utf8Decode bs = some cps`.
-/

namespace Solution.JSONExtract

namespace Utf8

open Specs.JSON
open Specs.Parser
open Serial

/-- `bs` decodes to `cps`, token by token. -/
def Utf8 (bs cps : List ℕ) : Prop :=
  ∃ toks : List (ℕ × List ℕ), Tokenizes codepoint toks ∧ (∀ t ∈ toks, t.2 ≠ []) ∧
    (toks.map (·.2)).flatten = bs ∧ toks.map (·.1) = cps

theorem utf8_nil : Utf8 [] [] := ⟨[], by intro it h; simp at h, by intro t h; simp at h, rfl, rfl⟩

theorem utf8_append {b1 c1 b2 c2 : List ℕ} (h1 : Utf8 b1 c1) (h2 : Utf8 b2 c2) :
    Utf8 (b1 ++ b2) (c1 ++ c2) := by
  obtain ⟨t1, ht1, hn1, hb1, hc1⟩ := h1
  obtain ⟨t2, ht2, hn2, hb2, hc2⟩ := h2
  refine ⟨t1 ++ t2, ?_, ?_, ?_, ?_⟩
  · intro it hit rest
    rcases List.mem_append.mp hit with h | h
    · exact ht1 it h rest
    · exact ht2 it h rest
  · intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact hn1 t h
    · exact hn2 t h
  · simp [← hb1, ← hb2]
  · simp [← hc1, ← hc2]

/-- A one-token decoding. -/
theorem utf8_tok {tok : List ℕ} {cp : ℕ} (hne : tok ≠ [])
    (h : ∀ rest, codepoint (tok ++ rest) = some (cp, rest)) : Utf8 tok [cp] :=
  ⟨[(cp, tok)], by intro it hit rest; simp only [List.mem_singleton] at hit; subst hit; exact h rest,
    by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact hne, by simp, by simp⟩

theorem codepoint_ascii {b : ℕ} (h : b < 0x80) (rest : List ℕ) :
    codepoint (b :: rest) = some (b, rest) := by
  have hb : isAscii b = true := by simp [isAscii, h]
  simp [codepoint, hb]

theorem utf8_ascii {b : ℕ} (h : b < 0x80) : Utf8 [b] [b] :=
  utf8_tok (by simp) (fun rest => codepoint_ascii h rest)

theorem utf8_asciiList : ∀ {l : List ℕ}, (∀ b ∈ l, b < 0x80) → Utf8 l l := by
  intro l
  induction l with
  | nil => intro _; exact utf8_nil
  | cons b l ih =>
    intro h
    have := utf8_append (utf8_ascii (h b (List.mem_cons_self ..)))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
    simpa using this

/-- Bounded repetition over a run of tokens never runs out of fuel. -/
theorem length_le_flatten {α : Type} (items : List (α × List ℕ)) (rest : List ℕ)
    (hne : ∀ t ∈ items, t.2 ≠ []) :
    items.length ≤ ((items.map (·.2)).flatten ++ rest).length := by
  induction items with
  | nil => simp
  | cons it items ih =>
    have h1 : it.2 ≠ [] := hne it (List.mem_cons_self ..)
    have h2 := ih fun t ht => hne t (List.mem_cons_of_mem _ ht)
    simp only [List.map_cons, List.flatten_cons, List.length_cons, List.append_assoc,
      List.length_append] at *
    have : 1 ≤ it.2.length := by
      cases hx : it.2 with
      | nil => exact absurd hx h1
      | cons a l => simp
    omega

theorem codepoint_nil : codepoint ([] : List ℕ) = none := rfl

theorem utf8_decode {bs cps : List ℕ} (h : Utf8 bs cps) : utf8Decode bs = some cps := by
  obtain ⟨toks, ht, hn, hb, hc⟩ := h
  have hmany : manyUpTo bs.length codepoint bs = some (cps, []) := by
    rw [← hb, ← hc]
    have := manyUpTo_append (p := codepoint) (items := toks) (rest := [])
      ht codepoint_nil (n := ((toks.map (fun t : ℕ × List ℕ => t.2)).flatten ++ []).length)
      (length_le_flatten toks [] hn)
    simpa using this
  rw [utf8Decode, seqLeft_apply, many_apply, hmany]
  rfl

/-! ## The code points of a string-body element -/

theorem codepoint_u2 {b0 b1 : ℕ} (h0 : Model.isLead2 b0 = true) (h1 : Model.isCont b1 = true)
    (rest : List ℕ) :
    codepoint (b0 :: b1 :: rest) = some ((b0 - 0xC0) * 0x40 + (b1 - 0x80), rest) := by
  have hb0 : 0xC2 ≤ b0 ∧ b0 ≤ 0xDF := by
    simpa only [Model.isLead2, Bool.and_eq_true, decide_eq_true_eq] using h0
  have hb1 : 0x80 ≤ b1 ∧ b1 ≤ 0xBF := by
    simpa only [Model.isCont, Bool.and_eq_true, decide_eq_true_eq] using h1
  have ha : isAscii b0 = false := by simp [isAscii]; omega
  have hl2 : isLead2 b0 = true := by simp [isLead2]; omega
  have hc : isContinuation b1 = true := by simp [isContinuation]; omega
  simp [codepoint, continuation, ha, hl2, hc]

theorem codepoint_u3 {b0 b1 b2 : ℕ}
    (hl : (b0 = 0xE0 ∧ Model.isContA0BF b1 = true) ∨
      (Model.isLead3 b0 = true ∧ Model.isCont b1 = true) ∨
      (b0 = 0xED ∧ Model.isCont809F b1 = true))
    (h2 : Model.isCont b2 = true) (rest : List ℕ) :
    codepoint (b0 :: b1 :: b2 :: rest)
      = some ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80), rest) := by
  have hb2 : 0x80 ≤ b2 ∧ b2 ≤ 0xBF := by
    simpa only [Model.isCont, Bool.and_eq_true, decide_eq_true_eq] using h2
  have hbound : (0xE0 ≤ b0 ∧ b0 ≤ 0xEF) ∧ (0x80 ≤ b1 ∧ b1 ≤ 0xBF) ∧
      0x800 ≤ (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80) ∧
      ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80) < 0xD800 ∨
        0xDFFF < (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) := by
    rcases hl with ⟨rfl, hb1⟩ | ⟨hb0, hb1⟩ | ⟨rfl, hb1⟩
    · have hb1' : 0xA0 ≤ b1 ∧ b1 ≤ 0xBF := by
        simpa only [Model.isContA0BF, Bool.and_eq_true, decide_eq_true_eq] using hb1
      refine ⟨by omega, by omega, by omega, Or.inl (by omega)⟩
    · have hb0' : (0xE1 ≤ b0 ∧ b0 ≤ 0xEC) ∨ (0xEE ≤ b0 ∧ b0 ≤ 0xEF) := by
        simpa only [Model.isLead3, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using hb0
      have hb1' : 0x80 ≤ b1 ∧ b1 ≤ 0xBF := by
        simpa only [Model.isCont, Bool.and_eq_true, decide_eq_true_eq] using hb1
      rcases hb0' with h | h
      · refine ⟨by omega, by omega, by omega, ?_⟩
        rcases Nat.lt_or_ge b0 0xED with hh | hh
        · left; omega
        · right; omega
      · refine ⟨by omega, by omega, by omega, Or.inr (by omega)⟩
    · have hb1' : 0x80 ≤ b1 ∧ b1 ≤ 0x9F := by
        simpa only [Model.isCont809F, Bool.and_eq_true, decide_eq_true_eq] using hb1
      refine ⟨by omega, by omega, by omega, Or.inl (by omega)⟩
  obtain ⟨hb0, hb1, hge, hsur⟩ := hbound
  have ha : isAscii b0 = false := by simp [isAscii]; omega
  have hl2 : isLead2 b0 = false := by simp [isLead2]; omega
  have hl3 : isLead3 b0 = true := by simp [isLead3]; omega
  have hc1 : isContinuation b1 = true := by simp [isContinuation]; omega
  have hc2 : isContinuation b2 = true := by simp [isContinuation]; omega
  have hguard : ¬ ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80) < 0x800 ∨
      isSurrogate ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) = true) := by
    simp only [isSurrogate, isHighSurrogate, isLowSurrogate, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    push_neg
    refine ⟨by omega, ?_, ?_⟩ <;> (intro hx; omega)
  simp [codepoint, continuation, ha, hl2, hl3, hc1, hc2, hguard]

theorem codepoint_u4 {b0 b1 b2 b3 : ℕ}
    (hl : (b0 = 0xF0 ∧ Model.isCont90BF b1 = true) ∨
      (Model.isLead4 b0 = true ∧ Model.isCont b1 = true) ∨
      (b0 = 0xF4 ∧ Model.isCont808F b1 = true))
    (h2 : Model.isCont b2 = true) (h3 : Model.isCont b3 = true) (rest : List ℕ) :
    codepoint (b0 :: b1 :: b2 :: b3 :: rest)
      = some ((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80),
          rest) := by
  have hb2 : 0x80 ≤ b2 ∧ b2 ≤ 0xBF := by
    simpa only [Model.isCont, Bool.and_eq_true, decide_eq_true_eq] using h2
  have hb3 : 0x80 ≤ b3 ∧ b3 ≤ 0xBF := by
    simpa only [Model.isCont, Bool.and_eq_true, decide_eq_true_eq] using h3
  have hbound : (0xF0 ≤ b0 ∧ b0 ≤ 0xF4) ∧ (0x80 ≤ b1 ∧ b1 ≤ 0xBF) ∧
      0x10000 ≤ (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80) ∧
      (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80)
        ≤ 0x10FFFF := by
    rcases hl with ⟨rfl, hb1⟩ | ⟨hb0, hb1⟩ | ⟨rfl, hb1⟩
    · have hb1' : 0x90 ≤ b1 ∧ b1 ≤ 0xBF := by
        simpa only [Model.isCont90BF, Bool.and_eq_true, decide_eq_true_eq] using hb1
      exact ⟨by omega, by omega, by omega, by omega⟩
    · have hb0' : 0xF1 ≤ b0 ∧ b0 ≤ 0xF3 := by
        simpa only [Model.isLead4, Bool.and_eq_true, decide_eq_true_eq] using hb0
      have hb1' : 0x80 ≤ b1 ∧ b1 ≤ 0xBF := by
        simpa only [Model.isCont, Bool.and_eq_true, decide_eq_true_eq] using hb1
      exact ⟨by omega, by omega, by omega, by omega⟩
    · have hb1' : 0x80 ≤ b1 ∧ b1 ≤ 0x8F := by
        simpa only [Model.isCont808F, Bool.and_eq_true, decide_eq_true_eq] using hb1
      exact ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨hb0, hb1, hge, hle⟩ := hbound
  have ha : isAscii b0 = false := by simp [isAscii]; omega
  have hl2 : isLead2 b0 = false := by simp [isLead2]; omega
  have hl3 : isLead3 b0 = false := by simp [isLead3]; omega
  have hl4 : isLead4 b0 = true := by simp [isLead4]; omega
  have hc1 : isContinuation b1 = true := by simp [isContinuation]; omega
  have hc2 : isContinuation b2 = true := by simp [isContinuation]; omega
  have hc3 : isContinuation b3 = true := by simp [isContinuation]; omega
  have hguard : ¬ ((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
        + (b3 - 0x80) < 0x10000 ∨
      0x10FFFF < (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
        + (b3 - 0x80)) := by
    push_neg
    exact ⟨by omega, by omega⟩
  simp [codepoint, continuation, ha, hl2, hl3, hl4, hc1, hc2, hc3, hguard]

theorem utf8_se {e : SE} (h : e.WF) : Utf8 e.bytes e.dcps := by
  cases e with
  | plain b =>
    have hu : Model.isUnescaped b = true := h
    have hb : b < 0x80 := by
      simp only [Model.isUnescaped, Bool.and_eq_true, decide_eq_true_eq] at hu
      omega
    exact utf8_ascii hb
  | esc b =>
    have hs : Model.isSimpleEsc b = true := h
    have hb : b < 0x80 := by
      simp only [Model.isSimpleEsc, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with ((((((h|h)|h)|h)|h)|h)|h)|h <;> subst h <;> decide
    have := utf8_append (utf8_ascii (show backslash < 0x80 by decide)) (utf8_ascii hb)
    simpa [SE.bytes, SE.dcps] using this
  | hex a b c d =>
    obtain ⟨ha, hb, hc, hd⟩ := h
    have hlt : ∀ x : ℕ, Model.isHex x = true → x < 0x80 := by
      intro x hx
      simp only [Model.isHex, Model.isDigit, Model.isUpperHex, Model.isLowerHex, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at hx
      rcases hx with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩ <;>
        [show x < 0x80; show x < 0x80; show x < 0x80] <;>
        [(have : x ≤ 0x39 := h2); (have : x ≤ 0x46 := h2); (have : x ≤ 0x66 := h2)] <;> omega
    refine utf8_asciiList ?_
    intro x hx
    simp only [SE.bytes, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · exact hlt _ ha
    · exact hlt _ hb
    · exact hlt _ hc
    · exact hlt _ hd
  | u2 b0 b1 =>
    obtain ⟨h0, h1⟩ := h
    exact utf8_tok (by simp [SE.bytes]) (fun rest => codepoint_u2 h0 h1 rest)
  | u3 b0 b1 b2 =>
    obtain ⟨hl, h2⟩ := h
    exact utf8_tok (by simp [SE.bytes]) (fun rest => codepoint_u3 hl h2 rest)
  | u4 b0 b1 b2 b3 =>
    obtain ⟨hl, h2, h3⟩ := h
    exact utf8_tok (by simp [SE.bytes]) (fun rest => codepoint_u4 hl h2 h3 rest)

theorem utf8_seList : ∀ {l : List SE}, (∀ e ∈ l, e.WF) → Utf8 (seBytes l) (dcpsList l) := by
  intro l
  induction l with
  | nil => intro _; exact utf8_nil
  | cons e l ih =>
    intro h
    have := utf8_append (utf8_se (h e (List.mem_cons_self ..)))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
    simpa [seBytes, dcpsList] using this

end Utf8

end Solution.JSONExtract
