import Solution.JSONExtract.SerToken

/-!
# A Google ID token is a serialization (`JSONExtract`)

The backward half of the specification argument: if `Specs.JSON.parseBytes bs`
succeeds with a token of the Google schema then `bs` is `Ser.bytes` of a
well-formed `Ser`.  This file inverts the two stages of the specification: the
UTF-8 decoder (`Dec`) and the combinator grammar.
-/

namespace Solution.JSONExtract

namespace ParseInv

open Specs
open Specs.JSON
open Specs.Parser
open Serial
open SerParse
open Model (Claim nClaims claimName claimCap isStrClaim isIntClaim)

/-! ## The branches of `codepoint` -/

def cpLead2 : Parser ℕ := do
  let b0 ← satisfy isLead2
  let b1 ← continuation
  pure ((b0 - 0xC0) * 0x40 + b1)

def cpLead3 : Parser ℕ := do
  let b0 ← satisfy isLead3
  let b1 ← continuation
  let b2 ← continuation
  let cp := (b0 - 0xE0) * 0x1000 + b1 * 0x40 + b2
  if cp < 0x800 || isSurrogate cp then failure else pure cp

def cpLead4 : Parser ℕ := do
  let b0 ← satisfy isLead4
  let b1 ← continuation
  let b2 ← continuation
  let b3 ← continuation
  let cp := (b0 - 0xF0) * 0x40000 + b1 * 0x1000 + b2 * 0x40 + b3
  if cp < 0x10000 || 0x10FFFF < cp then failure else pure cp

theorem codepoint_eq (l : List ℕ) :
    codepoint l = orElse (satisfy isAscii) (orElse cpLead2 (orElse cpLead3 cpLead4)) l := rfl

theorem satisfy_inv {q : ℕ → Bool} {l : List ℕ} {a : ℕ} {r : List ℕ}
    (h : satisfy q l = some (a, r)) : l = a :: r ∧ q a = true := by
  cases l with
  | nil => simp at h
  | cons b t =>
    rw [satisfy_cons] at h
    split at h
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨by rw [← h.1, ← h.2], by rw [← h.1]; assumption⟩
    · simp at h

theorem continuation_inv {l : List ℕ} {a : ℕ} {r : List ℕ} (h : continuation l = some (a, r)) :
    ∃ b, l = b :: r ∧ isContinuation b = true ∧ a = b - 0x80 := by
  rw [continuation, map_apply] at h
  cases hs : satisfy isContinuation l with
  | none => rw [hs] at h; simp at h
  | some ar =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hl, hq⟩ := satisfy_inv hs
    exact ⟨ar.1, by rw [hl, ← h.2], hq, h.1.symm⟩

theorem cpLead2_inv {l : List ℕ} {cp : ℕ} {r : List ℕ} (h : cpLead2 l = some (cp, r)) :
    ∃ b0 b1, l = b0 :: b1 :: r ∧ isLead2 b0 = true ∧ isContinuation b1 = true ∧
      cp = (b0 - 0xC0) * 0x40 + (b1 - 0x80) := by
  rw [cpLead2, bind_apply] at h
  cases h0 : satisfy isLead2 l with
  | none => rw [h0] at h; simp at h
  | some a0 =>
    rw [h0] at h
    simp only [Option.bind_some, bind_apply] at h
    cases h1 : continuation a0.2 with
    | none => rw [h1] at h; simp at h
    | some a1 =>
      rw [h1] at h
      simp only [Option.bind_some, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hl0, hq0⟩ := satisfy_inv h0
      obtain ⟨b1, hl1, hq1, ha1⟩ := continuation_inv h1
      exact ⟨a0.1, b1, by rw [hl0, hl1, ← h.2], hq0, hq1, by rw [← h.1, ha1]⟩

theorem cpLead3_inv {l : List ℕ} {cp : ℕ} {r : List ℕ} (h : cpLead3 l = some (cp, r)) :
    ∃ b0 b1 b2, l = b0 :: b1 :: b2 :: r ∧ isLead3 b0 = true ∧ isContinuation b1 = true ∧
      isContinuation b2 = true ∧
      cp = (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80) ∧
      0x800 ≤ cp ∧ isSurrogate cp = false := by
  rw [cpLead3, bind_apply] at h
  cases h0 : satisfy isLead3 l with
  | none => rw [h0] at h; simp at h
  | some a0 =>
    rw [h0] at h
    simp only [Option.bind_some, bind_apply] at h
    cases h1 : continuation a0.2 with
    | none => rw [h1] at h; simp at h
    | some a1 =>
      rw [h1] at h
      simp only [Option.bind_some, bind_apply] at h
      cases h2 : continuation a1.2 with
      | none => rw [h2] at h; simp at h
      | some a2 =>
        rw [h2] at h
        simp only [Option.bind_some] at h
        split at h
        · simp at h
        · next hg =>
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl0, hq0⟩ := satisfy_inv h0
          obtain ⟨b1, hl1, hq1, ha1⟩ := continuation_inv h1
          obtain ⟨b2, hl2, hq2, ha2⟩ := continuation_inv h2
          have hcp : cp = (a0.1 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80) := by
            rw [← h.1, ha1, ha2]
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hg
          rw [ha1, ha2] at hg
          exact ⟨a0.1, b1, b2, by rw [hl0, hl1, hl2, ← h.2], hq0, hq1, hq2, hcp,
            by rw [hcp]; omega, by rw [hcp]; exact hg.2⟩

theorem cpLead4_inv {l : List ℕ} {cp : ℕ} {r : List ℕ} (h : cpLead4 l = some (cp, r)) :
    ∃ b0 b1 b2 b3, l = b0 :: b1 :: b2 :: b3 :: r ∧ isLead4 b0 = true ∧
      isContinuation b1 = true ∧ isContinuation b2 = true ∧ isContinuation b3 = true ∧
      cp = (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80) ∧
      0x10000 ≤ cp ∧ cp ≤ 0x10FFFF := by
  rw [cpLead4, bind_apply] at h
  cases h0 : satisfy isLead4 l with
  | none => rw [h0] at h; simp at h
  | some a0 =>
    rw [h0] at h
    simp only [Option.bind_some, bind_apply] at h
    cases h1 : continuation a0.2 with
    | none => rw [h1] at h; simp at h
    | some a1 =>
      rw [h1] at h
      simp only [Option.bind_some, bind_apply] at h
      cases h2 : continuation a1.2 with
      | none => rw [h2] at h; simp at h
      | some a2 =>
        rw [h2] at h
        simp only [Option.bind_some, bind_apply] at h
        cases h3 : continuation a2.2 with
        | none => rw [h3] at h; simp at h
        | some a3 =>
          rw [h3] at h
          simp only [Option.bind_some] at h
          split at h
          · simp at h
          · next hg =>
            simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hl0, hq0⟩ := satisfy_inv h0
            obtain ⟨b1, hl1, hq1, ha1⟩ := continuation_inv h1
            obtain ⟨b2, hl2, hq2, ha2⟩ := continuation_inv h2
            obtain ⟨b3, hl3, hq3, ha3⟩ := continuation_inv h3
            have hcp : cp = (a0.1 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
                + (b3 - 0x80) := by rw [← h.1, ha1, ha2, ha3]
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hg
            rw [ha1, ha2, ha3] at hg
            exact ⟨a0.1, b1, b2, b3, by rw [hl0, hl1, hl2, hl3, ← h.2], hq0, hq1, hq2, hq3, hcp,
              by rw [hcp]; omega, by rw [hcp]; omega⟩

theorem codepoint_inv {l : List ℕ} {cp : ℕ} {r : List ℕ} (h : codepoint l = some (cp, r)) :
    (∃ b, l = b :: r ∧ isAscii b = true ∧ cp = b) ∨
    (∃ b0 b1, l = b0 :: b1 :: r ∧ isLead2 b0 = true ∧ isContinuation b1 = true ∧
      cp = (b0 - 0xC0) * 0x40 + (b1 - 0x80)) ∨
    (∃ b0 b1 b2, l = b0 :: b1 :: b2 :: r ∧ isLead3 b0 = true ∧ isContinuation b1 = true ∧
      isContinuation b2 = true ∧
      cp = (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80) ∧
      0x800 ≤ cp ∧ isSurrogate cp = false) ∨
    (∃ b0 b1 b2 b3, l = b0 :: b1 :: b2 :: b3 :: r ∧ isLead4 b0 = true ∧
      isContinuation b1 = true ∧ isContinuation b2 = true ∧ isContinuation b3 = true ∧
      cp = (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80) ∧
      0x10000 ≤ cp ∧ cp ≤ 0x10FFFF) := by
  rw [codepoint_eq] at h
  cases hA : satisfy isAscii l with
  | some ar =>
    rw [orElse_apply_of_some hA] at h
    obtain ⟨b, t⟩ := ar
    rw [Option.some.injEq, Prod.mk.injEq] at h
    cases l with
    | nil => simp at hA
    | cons b0 t0 =>
      rw [satisfy_cons] at hA
      split at hA
      · rw [Option.some.injEq, Prod.mk.injEq] at hA
        exact Or.inl ⟨b0, by rw [← h.2, ← hA.2], by assumption, by rw [← h.1, ← hA.1]⟩
      · simp at hA
  | none =>
    rw [orElse_apply_of_none hA] at h
    cases hB : cpLead2 l with
    | some br =>
      rw [orElse_apply_of_some hB] at h
      rw [Option.some.injEq] at h
      subst h
      exact Or.inr (Or.inl (cpLead2_inv hB))
    | none =>
      rw [orElse_apply_of_none hB] at h
      cases hC : cpLead3 l with
      | some cr =>
        rw [orElse_apply_of_some hC] at h
        rw [Option.some.injEq] at h
        subst h
        exact Or.inr (Or.inr (Or.inl (cpLead3_inv hC)))
      | none =>
        rw [orElse_apply_of_none hC] at h
        exact Or.inr (Or.inr (Or.inr (cpLead4_inv h)))

/-! ## Canonical UTF-8 encoding of a code point

UTF-8 is injective on the sequences `codepoint` accepts, so a byte list that
decodes to `cps` *is* the canonical encoding of `cps`.  That lets the rest of
the inversion work purely with code points: the byte equality of the final
serialization follows from `utf8_bytes` applied to `SerParse.utf8_ser`. -/

/-- The UTF-8 bytes of a code point. -/
def cpBytes (cp : ℕ) : List ℕ :=
  if cp < 0x80 then [cp]
  else if cp < 0x800 then [0xC0 + cp / 0x40, 0x80 + cp % 0x40]
  else if cp < 0x10000 then
    [0xE0 + cp / 0x1000, 0x80 + cp / 0x40 % 0x40, 0x80 + cp % 0x40]
  else
    [0xF0 + cp / 0x40000, 0x80 + cp / 0x1000 % 0x40, 0x80 + cp / 0x40 % 0x40, 0x80 + cp % 0x40]

/-- The UTF-8 bytes of a list of code points. -/
def bytesOfCps (cps : List ℕ) : List ℕ := (cps.map cpBytes).flatten

@[simp] theorem bytesOfCps_nil : bytesOfCps [] = [] := rfl

theorem bytesOfCps_cons (c : ℕ) (l : List ℕ) :
    bytesOfCps (c :: l) = cpBytes c ++ bytesOfCps l := by simp [bytesOfCps]

theorem bytesOfCps_append (l1 l2 : List ℕ) :
    bytesOfCps (l1 ++ l2) = bytesOfCps l1 ++ bytesOfCps l2 := by
  simp [bytesOfCps]

theorem cpBytes_ascii {c : ℕ} (h : c < 0x80) : cpBytes c = [c] := by rw [cpBytes, if_pos h]

theorem bytesOfCps_ascii : ∀ {l : List ℕ}, (∀ c ∈ l, c < 0x80) → bytesOfCps l = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons c l ih =>
    intro h
    rw [bytesOfCps_cons, cpBytes_ascii (h c (List.mem_cons_self ..)),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- A code point the decoder can produce. -/
def ValidCp (c : ℕ) : Prop := c < 0x80 ∨ (0x80 ≤ c ∧ c ≤ 0x10FFFF ∧ isSurrogate c = false)

theorem validCp_of_lt {c : ℕ} (h : c < 0x80) : ValidCp c := Or.inl h

theorem cpBytes_u2 {b0 b1 : ℕ} (h0 : isLead2 b0 = true) (h1 : isContinuation b1 = true) :
    cpBytes ((b0 - 0xC0) * 0x40 + (b1 - 0x80)) = [b0, b1] := by
  simp only [isLead2, Bool.and_eq_true, decide_eq_true_eq] at h0
  simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at h1
  rw [cpBytes, if_neg (by omega), if_pos (by omega),
    show 0xC0 + ((b0 - 0xC0) * 0x40 + (b1 - 0x80)) / 0x40 = b0 by omega,
    show 0x80 + ((b0 - 0xC0) * 0x40 + (b1 - 0x80)) % 0x40 = b1 by omega]

theorem valid_u2 {b0 b1 : ℕ} (h0 : isLead2 b0 = true) (h1 : isContinuation b1 = true) :
    ValidCp ((b0 - 0xC0) * 0x40 + (b1 - 0x80)) := by
  simp only [isLead2, Bool.and_eq_true, decide_eq_true_eq] at h0
  simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at h1
  refine Or.inr ⟨by omega, by omega, ?_⟩
  simp only [isSurrogate, isHighSurrogate, isLowSurrogate, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
  omega

theorem cpBytes_u3 {b0 b1 b2 : ℕ} (h0 : isLead3 b0 = true) (h1 : isContinuation b1 = true)
    (h2 : isContinuation b2 = true)
    (hge : 0x800 ≤ (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) :
    cpBytes ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) = [b0, b1, b2] := by
  simp only [isLead3, Bool.and_eq_true, decide_eq_true_eq] at h0
  simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at h1
  simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at h2
  rw [cpBytes, if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 0xE0 + ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) / 0x1000 = b0 by omega,
    show 0x80 + ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) / 0x40 % 0x40 = b1 by
      omega,
    show 0x80 + ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) % 0x40 = b2 by omega]

theorem valid_u3 {b0 b1 b2 : ℕ} (h0 : isLead3 b0 = true) (h1 : isContinuation b1 = true)
    (h2 : isContinuation b2 = true)
    (hge : 0x800 ≤ (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80))
    (hs : isSurrogate ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) = false) :
    ValidCp ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) := by
  simp only [isLead3, Bool.and_eq_true, decide_eq_true_eq] at h0
  simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at h1
  simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at h2
  exact Or.inr ⟨by omega, by omega, hs⟩

theorem cpBytes_u4 {b0 b1 b2 b3 : ℕ} (h0 : isLead4 b0 = true) (h1 : isContinuation b1 = true)
    (h2 : isContinuation b2 = true) (h3 : isContinuation b3 = true)
    (hge : 0x10000 ≤ (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
      + (b3 - 0x80)) :
    cpBytes ((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80))
      = [b0, b1, b2, b3] := by
  simp only [isLead4, Bool.and_eq_true, decide_eq_true_eq] at h0
  simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at h1
  simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at h2
  simp only [isContinuation, Bool.and_eq_true, decide_eq_true_eq] at h3
  rw [cpBytes, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show 0xF0 + ((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
      + (b3 - 0x80)) / 0x40000 = b0 by omega,
    show 0x80 + ((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
      + (b3 - 0x80)) / 0x1000 % 0x40 = b1 by omega,
    show 0x80 + ((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
      + (b3 - 0x80)) / 0x40 % 0x40 = b2 by omega,
    show 0x80 + ((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
      + (b3 - 0x80)) % 0x40 = b3 by omega]

theorem valid_u4 {b0 b1 b2 b3 : ℕ} (h0 : isLead4 b0 = true) (h1 : isContinuation b1 = true)
    (h2 : isContinuation b2 = true) (h3 : isContinuation b3 = true)
    (hge : 0x10000 ≤ (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
      + (b3 - 0x80))
    (hle : (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80)
      ≤ 0x10FFFF) :
    ValidCp ((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80)) := by
  refine Or.inr ⟨by omega, hle, ?_⟩
  simp only [isSurrogate, isHighSurrogate, isLowSurrogate, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
  omega

set_option maxRecDepth 10000 in
/-- One `codepoint` token: the bytes it consumed are the canonical encoding of
the code point it produced. -/
theorem cp_seg {l : List ℕ} {cp : ℕ} {r : List ℕ} (h : codepoint l = some (cp, r)) :
    l = cpBytes cp ++ r ∧ ValidCp cp := by
  rcases codepoint_inv h with ⟨b, hl, hq, rfl⟩ | ⟨b0, b1, hl, h0, h1, rfl⟩ |
    ⟨b0, b1, b2, hl, h0, h1, h2, rfl, hge, hs⟩ | ⟨b0, b1, b2, b3, hl, h0, h1, h2, h3, rfl, hge, hle⟩
  · have hb : cp < 0x80 := by simpa only [isAscii, decide_eq_true_eq] using hq
    exact ⟨by rw [hl, cpBytes_ascii hb]; rfl, validCp_of_lt hb⟩
  · exact ⟨by rw [hl, cpBytes_u2 h0 h1]; rfl, valid_u2 h0 h1⟩
  · exact ⟨by rw [hl, cpBytes_u3 h0 h1 h2 hge]; rfl, valid_u3 h0 h1 h2 hge hs⟩
  · exact ⟨by rw [hl, cpBytes_u4 h0 h1 h2 h3 hge]; rfl, valid_u4 h0 h1 h2 h3 hge hle⟩

/-- A decoding is the canonical encoding read backwards. -/
theorem utf8_bytes {bs cps : List ℕ} (h : Utf8.Utf8 bs cps) : bs = bytesOfCps cps := by
  obtain ⟨toks, ht, -, hb, hc⟩ := h
  rw [← hb, ← hc]
  clear hb hc
  induction toks with
  | nil => rfl
  | cons t ts ih =>
    have h1 := ht t (List.mem_cons_self ..) []
    rw [List.append_nil] at h1
    have h2 := (cp_seg h1).1
    rw [List.append_nil] at h2
    rw [List.map_cons, List.flatten_cons, List.map_cons, bytesOfCps_cons, ← h2,
      ih fun x hx => ht x (List.mem_cons_of_mem _ hx)]

theorem manyCp_inv : ∀ (n : ℕ) {l cs r : List ℕ},
    manyUpTo n codepoint l = some (cs, r) → l = bytesOfCps cs ++ r ∧ ∀ c ∈ cs, ValidCp c := by
  intro n
  induction n with
  | zero =>
    intro l cs r h
    simp only [manyUpTo_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp⟩
  | succ n ih =>
    intro l cs r h
    rw [manyUpTo_succ] at h
    cases hp : codepoint l with
    | none =>
      rw [hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, by simp⟩
    | some ar =>
      obtain ⟨c, r1⟩ := ar
      rw [hp] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨cs', r'⟩, hrec, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨hl, hv⟩ := cp_seg hp
      obtain ⟨hl', hv'⟩ := ih hrec
      refine ⟨?_, ?_⟩
      · rw [hl, hl', bytesOfCps_cons, List.append_assoc]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hv
        · exact hv' x hx

theorem utf8Decode_inv {bs cps : List ℕ} (h : utf8Decode bs = some cps) :
    bs = bytesOfCps cps ∧ ∀ c ∈ cps, ValidCp c := by
  rw [utf8Decode, seqLeft_apply, many_apply] at h
  cases hm : manyUpTo bs.length codepoint bs with
  | none => rw [hm] at h; simp at h
  | some ar =>
    obtain ⟨cs, r⟩ := ar
    rw [hm] at h
    cases r with
    | cons c t => simp at h
    | nil =>
      simp only [Option.bind_some, eof_nil, Option.map_some, Option.map_some,
        Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := manyCp_inv _ hm
      exact ⟨by rw [h1, List.append_nil], h2⟩


/-! ## The string-body element of a non-ASCII code point -/

/-- The UTF-8 sequence element of a non-ASCII code point. -/
def seOfCp (cp : ℕ) : SE :=
  if cp < 0x800 then .u2 (0xC0 + cp / 0x40) (0x80 + cp % 0x40)
  else if cp < 0x10000 then
    .u3 (0xE0 + cp / 0x1000) (0x80 + cp / 0x40 % 0x40) (0x80 + cp % 0x40)
  else
    .u4 (0xF0 + cp / 0x40000) (0x80 + cp / 0x1000 % 0x40) (0x80 + cp / 0x40 % 0x40)
      (0x80 + cp % 0x40)

theorem seOfCp_scp {cp : ℕ} (h : 0x80 ≤ cp) : (seOfCp cp).scp = cp := by
  by_cases h1 : cp < 0x800
  · rw [seOfCp, if_pos h1]; show (0xC0 + cp / 0x40 - 0xC0) * 0x40 + (0x80 + cp % 0x40 - 0x80) = cp
    omega
  · by_cases h2 : cp < 0x10000
    · rw [seOfCp, if_neg h1, if_pos h2]
      show (0xE0 + cp / 0x1000 - 0xE0) * 0x1000 + (0x80 + cp / 0x40 % 0x40 - 0x80) * 0x40
        + (0x80 + cp % 0x40 - 0x80) = cp
      omega
    · rw [seOfCp, if_neg h1, if_neg h2]
      show (0xF0 + cp / 0x40000 - 0xF0) * 0x40000 + (0x80 + cp / 0x1000 % 0x40 - 0x80) * 0x1000
        + (0x80 + cp / 0x40 % 0x40 - 0x80) * 0x40 + (0x80 + cp % 0x40 - 0x80) = cp
      omega

theorem seOfCp_dcps_scp (cp : ℕ) : (seOfCp cp).dcps = [(seOfCp cp).scp] := by
  unfold seOfCp
  split
  · rfl
  · split <;> rfl

theorem seOfCp_dcps {cp : ℕ} (h : 0x80 ≤ cp) : (seOfCp cp).dcps = [cp] := by
  rw [seOfCp_dcps_scp, seOfCp_scp h]

theorem seOfCp_mcp (cp : ℕ) : (seOfCp cp).mcp = Model.nonAsciiMarker := by
  unfold seOfCp; split; · rfl
  split <;> rfl

theorem seOfCp_isHigh (cp : ℕ) : (seOfCp cp).isHigh = false := by
  unfold seOfCp; split; · rfl
  split <;> rfl

theorem seOfCp_isLow (cp : ℕ) : (seOfCp cp).isLow = false := by
  unfold seOfCp; split; · rfl
  split <;> rfl

theorem seOfCp_WF {cp : ℕ} (h : 0x80 ≤ cp) (hv : ValidCp cp) : (seOfCp cp).WF := by
  rcases hv with h' | ⟨-, hle, hs⟩
  · omega
  · have hns : cp < 0xD800 ∨ 0xDFFF < cp := by
      simp only [isSurrogate, isHighSurrogate, isLowSurrogate, Bool.or_eq_false_iff,
        Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le] at hs
      rcases hs.1 with h1 | h1
      · left; omega
      · rcases hs.2 with h2 | h2
        · right; omega
        · right; omega
    by_cases h1 : cp < 0x800
    · rw [seOfCp, if_pos h1]
      refine ⟨?_, ?_⟩ <;>
        simp only [Model.isLead2, Model.isCont, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · by_cases h2 : cp < 0x10000
      · rw [seOfCp, if_neg h1, if_pos h2]
        refine ⟨?_, ?_⟩
        · simp only [Model.isLead3, Model.isContA0BF, Model.isCont, Model.isCont809F,
            Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
          rcases Nat.lt_or_ge cp 0x1000 with hc | hc
          · exact Or.inl ⟨by omega, by omega, by omega⟩
          · rcases Nat.lt_or_ge cp 0xD000 with hd | hd
            · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
            · rcases Nat.lt_or_ge cp 0xE000 with he | he
              · rcases hns with hn | hn
                · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
                · omega
              · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
        · simp only [Model.isCont, Bool.and_eq_true, decide_eq_true_eq]; omega
      · rw [seOfCp, if_neg h1, if_neg h2]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Model.isLead4, Model.isCont90BF, Model.isCont, Model.isCont808F,
            Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
          rcases Nat.lt_or_ge cp 0x40000 with hc | hc
          · exact Or.inl ⟨by omega, by omega, by omega⟩
          · rcases Nat.lt_or_ge cp 0x100000 with hd | hd
            · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
            · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
        · simp only [Model.isCont, Bool.and_eq_true, decide_eq_true_eq]; omega
        · simp only [Model.isCont, Bool.and_eq_true, decide_eq_true_eq]; omega


end ParseInv

end Solution.JSONExtract
