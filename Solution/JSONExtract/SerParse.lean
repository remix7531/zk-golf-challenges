import Solution.JSONExtract.Utf8

/-!
# A serialization parses to its JSON value (`JSONExtract`)

The forward half of the specification argument: for a well-formed `Ser`,
`Specs.JSON.parseBytes sr.bytes = some sr.json`.  The proof goes through the
code-point list `Ser.cps` (`Utf8` for the first stage, the combinator lemmas of
`Specs.Parser` for the second).
-/

namespace Solution.JSONExtract

namespace SerParse

open Specs
open Specs.JSON
open Specs.Parser
open Serial
open Utf8
open Model (Claim nClaims claimName claimCap)

/-! ## The code points of a serialization -/

def SV.cps : SV → List ℕ
  | .str body => quote :: (dcpsList body ++ [quote])
  | .num n => n.bytes
  | .btrue => trueLit
  | .bfalse => falseLit
  | .null => nullLit

def SMem.cpsNoWs3 (m : SMem) : List ℕ :=
  m.ws0 ++ [quote] ++ dcpsList m.key ++ [quote] ++ m.ws1 ++ [colon] ++ m.ws2 ++ SV.cps m.val

def SMem.cps (m : SMem) : List ℕ := SMem.cpsNoWs3 m ++ m.ws3

def bodyCps (ms : List SMem) (we : List ℕ) : List ℕ :=
  match ms with
  | [] => we
  | m :: ms => SMem.cps m ++ (ms.map fun m' => comma :: SMem.cps m').flatten

def Ser.cps (sr : Ser) : List ℕ :=
  sr.pre ++ [lbrace] ++ bodyCps sr.body sr.wsEmpty ++ [rbrace] ++ sr.post

/-! ## The bytes decode to the code points -/

theorem ws_ascii {l : List ℕ} (h : IsWs l) : ∀ b ∈ l, b < 0x80 := by
  intro b hb
  have := h b hb
  simp only [Model.isWs, Bool.or_eq_true, beq_iff_eq] at this
  rcases this with ((h1 | h1) | h1) | h1 <;> subst h1 <;> decide

theorem utf8_ws {l : List ℕ} (h : IsWs l) : Utf8 l l := utf8_asciiList (ws_ascii h)

theorem snum_ascii {nm : SNum} (h : nm.WF) : ∀ b ∈ nm.bytes, b < 0x80 := by
  obtain ⟨hint, hfrac, hexp⟩ := h
  have hdig : ∀ (ds : List ℕ), (∀ x ∈ ds, x ≤ 9) → ∀ b ∈ ds.map (· + digit0), b < 0x80 := by
    intro ds hds b hb
    simp only [List.mem_map] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have := hds x hx
    show x + 0x30 < 0x80
    omega
  have hints : ∀ x ∈ nm.ints, x ≤ 9 := by
    rcases hint with h1 | ⟨d, ds, h1, h2, h3, h4⟩
    · rw [h1]; intro x hx; simp only [List.mem_singleton] at hx; omega
    · rw [h1]; intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact h4 x hx
  intro b hb
  rw [SNum.bytes] at hb
  simp only [List.mem_append] at hb
  rcases hb with ((hb | hb) | hb) | hb
  · split at hb
    · simp only [List.mem_singleton] at hb; subst hb; decide
    · simp at hb
  · exact hdig _ hints b hb
  · split at hb
    · simp at hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · decide
      · exact hdig _ hfrac b hb
  · cases hx : nm.exp with
    | none => rw [hx] at hb; simp at hb
    | some e =>
      rw [hx] at hb hexp
      obtain ⟨hl, hs, hne, hdg⟩ := hexp
      simp only [SExp.bytes] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rcases hl with h1 | h1 <;> rw [h1] <;> decide
      · simp only [List.mem_append] at hb
        rcases hb with hb | hb
        · cases hsn : e.sign with
          | none => rw [hsn] at hb; simp at hb
          | some sg =>
            rw [hsn] at hb hs
            simp only [List.mem_singleton] at hb
            subst hb
            rcases hs with h1 | h1 <;> rw [h1] <;> decide
        · exact hdig _ hdg b hb

theorem utf8_val {v : SV} (h : v.WF) : Utf8 v.bytes (SV.cps v) := by
  cases v with
  | str body =>
    have := utf8_append (utf8_ascii (show quote < 0x80 by decide))
      (utf8_append (utf8_seList h) (utf8_ascii (show quote < 0x80 by decide)))
    simpa [SV.bytes, SV.cps] using this
  | num nm => exact utf8_asciiList (snum_ascii h)
  | btrue => exact utf8_asciiList (by intro b hb; fin_cases hb <;> decide)
  | bfalse => exact utf8_asciiList (by intro b hb; fin_cases hb <;> decide)
  | null => exact utf8_asciiList (by intro b hb; fin_cases hb <;> decide)

theorem utf8_mem {m : SMem} (h : m.WF) : Utf8 m.bytes (SMem.cps m) := by
  obtain ⟨hws0, hws1, hws2, hws3, hkey, hvwf, _⟩ := h
  have := utf8_append (utf8_ws hws0)
    (utf8_append (utf8_ascii (show quote < 0x80 by decide))
      (utf8_append (utf8_seList hkey)
        (utf8_append (utf8_ascii (show quote < 0x80 by decide))
          (utf8_append (utf8_ws hws1)
            (utf8_append (utf8_ascii (show colon < 0x80 by decide))
              (utf8_append (utf8_ws hws2)
                (utf8_append (utf8_val hvwf) (utf8_ws hws3))))))))
  simpa [SMem.bytes, SMem.cps, SMem.cpsNoWs3, List.append_assoc] using this

theorem utf8_body : ∀ (ms : List SMem), (∀ m ∈ ms, m.WF) → ∀ (we : List ℕ), IsWs we →
    Utf8 (bodyBytes ms we) (bodyCps ms we) := by
  intro ms
  induction ms with
  | nil => intro _ we hwe; exact utf8_ws hwe
  | cons m ms ih =>
    intro hms we hwe
    have htail : Utf8 ((ms.map fun m' => comma :: m'.bytes).flatten)
        ((ms.map fun m' => comma :: SMem.cps m').flatten) := by
      clear ih
      induction ms with
      | nil => exact utf8_nil
      | cons m' ms' ih' =>
        have h1 := utf8_append (utf8_ascii (show comma < 0x80 by decide))
          (utf8_mem (hms m' (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
        have h2 := ih' fun x hx => hms x (by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
        have := utf8_append h1 h2
        simpa using this
    have := utf8_append (utf8_mem (hms m (List.mem_cons_self ..))) htail
    simpa [bodyBytes, bodyCps] using this

theorem utf8_ser {sr : Ser} (h : sr.SWF) : Utf8 sr.bytes (Ser.cps sr) := by
  obtain ⟨hpre, hwe, hpost, hms⟩ := h
  have := utf8_append (utf8_ws hpre)
    (utf8_append (utf8_ascii (show lbrace < 0x80 by decide))
      (utf8_append (utf8_body sr.body hms sr.wsEmpty hwe)
        (utf8_append (utf8_ascii (show rbrace < 0x80 by decide)) (utf8_ws hpost))))
  simpa [Ser.bytes, Ser.cps, List.append_assoc] using this

/-! ## Hex digits -/

theorem hex_bounds {c : ℕ} (h : Model.isHex c = true) :
    (0x30 ≤ c ∧ c ≤ 0x39) ∨ (0x41 ≤ c ∧ c ≤ 0x46) ∨ (0x61 ≤ c ∧ c ≤ 0x66) := by
  simp only [Model.isHex, Model.isDigit, Model.isUpperHex, Model.isLowerHex, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

theorem hexValue_eq {c : ℕ} (h : Model.isHex c = true) : hexValue c = Model.hexVal c := by
  have h' := hex_bounds h
  unfold hexValue Model.hexVal Specs.JSON.isDigit Model.isDigit Model.isUpperHex Model.isLowerHex
  simp only [Bool.and_eq_true, decide_eq_true_eq, show (upperA : ℕ) = 0x41 from rfl,
    show (upperF : ℕ) = 0x46 from rfl, show (lowerA : ℕ) = 0x61 from rfl,
    show (lowerF : ℕ) = 0x66 from rfl, show (digit0 : ℕ) = 0x30 from rfl,
    show (digit9 : ℕ) = 0x39 from rfl]
  split_ifs <;> omega

theorem isHexDigit_of {c : ℕ} (h : Model.isHex c = true) : isHexDigit c = true := by
  have h' := hex_bounds h
  unfold isHexDigit Specs.JSON.isDigit
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    show (upperA : ℕ) = 0x41 from rfl, show (upperF : ℕ) = 0x46 from rfl,
    show (lowerA : ℕ) = 0x61 from rfl, show (lowerF : ℕ) = 0x66 from rfl,
    show (digit0 : ℕ) = 0x30 from rfl, show (digit9 : ℕ) = 0x39 from rfl]
  omega

theorem hex4_eq {a b c d : ℕ} (ha : Model.isHex a = true) (hb : Model.isHex b = true)
    (hc : Model.isHex c = true) (hd : Model.isHex d = true) (rest : List ℕ) :
    hex4 (a :: b :: c :: d :: rest) = some (hexNum a b c d, rest) := by
  simp [hex4, isHexDigit_of ha, isHexDigit_of hb, isHexDigit_of hc, isHexDigit_of hd,
    hexValue_eq ha, hexValue_eq hb, hexValue_eq hc, hexValue_eq hd, hexNum]

/-! ## The surrogate look-ahead -/

/-- The look-ahead inside `unicodeEscape`. -/
def lowEsc : Parser ℕ := do
  byte backslash; byte lowerU
  let lo ← hex4
  if isLowSurrogate lo then pure lo else failure

theorem unicodeEscape_eq (l : List ℕ) : unicodeEscape l = (do
    byte lowerU
    let hi ← hex4
    if isHighSurrogate hi then
      let lo ← Parser.optional lowEsc
      match lo with
      | some lo => pure (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))
      | none => pure hi
    else pure hi) l := rfl

/-- `lowEsc` fails on this code-point list. -/
def NoLow (l : List ℕ) : Prop := lowEsc l = none

theorem noLow_nil : NoLow [] := rfl

theorem noLow_of_head {c : ℕ} (h : c ≠ backslash) (t : List ℕ) : NoLow (c :: t) := by
  simp [NoLow, lowEsc, h]

theorem noLow_of_esc {c : ℕ} (h : c ≠ lowerU) (t : List ℕ) : NoLow (backslash :: c :: t) := by
  simp [NoLow, lowEsc, h]

theorem noLow_of_hex {a b c d : ℕ} (ha : Model.isHex a = true) (hb : Model.isHex b = true)
    (hc : Model.isHex c = true) (hd : Model.isHex d = true)
    (hlow : isLowSurrogate (hexNum a b c d) = false) (t : List ℕ) :
    NoLow (backslash :: lowerU :: a :: b :: c :: d :: t) := by
  simp [NoLow, lowEsc, hex4_eq ha hb hc hd, hlow]

theorem lowEsc_pair {a b c d : ℕ} (ha : Model.isHex a = true) (hb : Model.isHex b = true)
    (hc : Model.isHex c = true) (hd : Model.isHex d = true)
    (hlow : isLowSurrogate (hexNum a b c d) = true) (t : List ℕ) :
    lowEsc (backslash :: lowerU :: a :: b :: c :: d :: t) = some (hexNum a b c d, t) := by
  simp [lowEsc, hex4_eq ha hb hc hd, hlow]

/-! ## Code-point bounds of the string-body elements -/

theorem u2_scp_ge {b0 b1 : ℕ} (h : Model.isLead2 b0 = true ∧ Model.isCont b1 = true) :
    0x80 ≤ (b0 - 0xC0) * 0x40 + (b1 - 0x80) := by
  have h0 : 0xC2 ≤ b0 ∧ b0 ≤ 0xDF := by
    simpa only [Model.isLead2, Bool.and_eq_true, decide_eq_true_eq] using h.1
  omega

theorem u3_scp_ge {b0 b1 b2 : ℕ}
    (hl : (b0 = 0xE0 ∧ Model.isContA0BF b1 = true) ∨
      (Model.isLead3 b0 = true ∧ Model.isCont b1 = true) ∨
      (b0 = 0xED ∧ Model.isCont809F b1 = true)) :
    0x80 ≤ (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80) := by
  rcases hl with ⟨rfl, hb1⟩ | ⟨hb0, _⟩ | ⟨rfl, hb1⟩
  · have : 0xA0 ≤ b1 ∧ b1 ≤ 0xBF := by
      simpa only [Model.isContA0BF, Bool.and_eq_true, decide_eq_true_eq] using hb1
    omega
  · have : (0xE1 ≤ b0 ∧ b0 ≤ 0xEC) ∨ (0xEE ≤ b0 ∧ b0 ≤ 0xEF) := by
      simpa only [Model.isLead3, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using hb0
    rcases this with h | h <;> omega
  · omega

theorem u4_scp_ge {b0 b1 b2 b3 : ℕ}
    (hl : (b0 = 0xF0 ∧ Model.isCont90BF b1 = true) ∨
      (Model.isLead4 b0 = true ∧ Model.isCont b1 = true) ∨
      (b0 = 0xF4 ∧ Model.isCont808F b1 = true)) :
    0x80 ≤ (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80) := by
  rcases hl with ⟨rfl, hb1⟩ | ⟨hb0, _⟩ | ⟨rfl, _⟩
  · have : 0x90 ≤ b1 ∧ b1 ≤ 0xBF := by
      simpa only [Model.isCont90BF, Bool.and_eq_true, decide_eq_true_eq] using hb1
    omega
  · have : 0xF1 ≤ b0 ∧ b0 ≤ 0xF3 := by
      simpa only [Model.isLead4, Bool.and_eq_true, decide_eq_true_eq] using hb0
    omega
  · omega

set_option maxRecDepth 100000 in
/-- Any element that is not a low `\uXXXX` escape makes the look-ahead fail. -/
theorem noLow_of_elem {e : SE} (h : e.WF) (hlow : e.isLow = false) (X : List ℕ) :
    NoLow (e.dcps ++ X) := by
  cases e with
  | plain b =>
    have hu : Model.isUnescaped b = true := h
    have hne : b ≠ backslash := by
      simp only [Model.isUnescaped, Bool.and_eq_true, bne_iff_ne, ne_eq] at hu
      exact hu.2
    show NoLow (b :: X)
    exact noLow_of_head hne X
  | esc b =>
    have hs : Model.isSimpleEsc b = true := h
    have hb : b ≠ lowerU := by
      simp only [Model.isSimpleEsc, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with ((((((h1|h1)|h1)|h1)|h1)|h1)|h1)|h1 <;> subst h1 <;> decide
    show NoLow (backslash :: b :: X)
    exact noLow_of_esc hb X
  | hex a b c d =>
    have h' : Model.isHex a = true ∧ Model.isHex b = true ∧ Model.isHex c = true ∧
        Model.isHex d = true := h
    have hl : isLowSurrogate (hexNum a b c d) = false := hlow
    show NoLow (backslash :: lowerU :: a :: b :: c :: d :: X)
    exact noLow_of_hex h'.1 h'.2.1 h'.2.2.1 h'.2.2.2 hl X
  | u2 b0 b1 =>
    have h' : Model.isLead2 b0 = true ∧ Model.isCont b1 = true := h
    have hge := u2_scp_ge h'
    have hne : (b0 - 0xC0) * 0x40 + (b1 - 0x80) ≠ 0x5C := by omega
    show NoLow (((b0 - 0xC0) * 0x40 + (b1 - 0x80)) :: X)
    exact noLow_of_head hne X
  | u3 b0 b1 b2 =>
    have h' : ((b0 = 0xE0 ∧ Model.isContA0BF b1 = true) ∨
        (Model.isLead3 b0 = true ∧ Model.isCont b1 = true) ∨
        (b0 = 0xED ∧ Model.isCont809F b1 = true)) ∧ Model.isCont b2 = true := h
    have hge := u3_scp_ge (b2 := b2) h'.1
    have hne : (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80) ≠ 0x5C := by omega
    show NoLow (((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) :: X)
    exact noLow_of_head hne X
  | u4 b0 b1 b2 b3 =>
    have h' : ((b0 = 0xF0 ∧ Model.isCont90BF b1 = true) ∨
        (Model.isLead4 b0 = true ∧ Model.isCont b1 = true) ∨
        (b0 = 0xF4 ∧ Model.isCont808F b1 = true)) ∧ Model.isCont b2 = true ∧
        Model.isCont b3 = true := h
    have hge := u4_scp_ge (b2 := b2) (b3 := b3) h'.1
    have hne : (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80)
        ≠ 0x5C := by omega
    show NoLow (((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
      + (b3 - 0x80)) :: X)
    exact noLow_of_head hne X

/-! ## One element of a string body -/

theorem isUnescaped_spec_of_model {b : ℕ} (h : Model.isUnescaped b = true) :
    Specs.JSON.isUnescaped b = true := by
  simp only [Model.isUnescaped, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  simp only [Specs.JSON.isUnescaped, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩

theorem isUnescaped_high {cp : ℕ} (h : 0x80 ≤ cp) : Specs.JSON.isUnescaped cp = true := by
  simp only [Specs.JSON.isUnescaped, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show (0x20 : ℕ) ≤ cp; omega
  · show cp ≠ 0x22; omega
  · show cp ≠ 0x5C; omega

theorem stringElem_plain {b : ℕ} (h : Model.isUnescaped b = true) (rest : List ℕ) :
    stringElem (b :: rest) = some (b, rest) := by
  simp [stringElem, isUnescaped_spec_of_model h]

theorem stringElem_high {cp : ℕ} (h : 0x80 ≤ cp) (rest : List ℕ) :
    stringElem (cp :: rest) = some (cp, rest) := by
  simp [stringElem, isUnescaped_high h]

theorem unesc_backslash : Specs.JSON.isUnescaped backslash = false := by decide

set_option maxHeartbeats 1000000 in
theorem stringElem_esc {b : ℕ} (h : Model.isSimpleEsc b = true) (rest : List ℕ) :
    stringElem (backslash :: b :: rest) = some (Model.escVal b, rest) := by
  simp only [Model.isSimpleEsc, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((((h1|h1)|h1)|h1)|h1)|h1)|h1)|h1 <;> subst h1 <;>
    simp [stringElem, escape, Model.escVal, unesc_backslash]

theorem escape_u_chain (l : List ℕ) : escape (lowerU :: l) = unicodeEscape (lowerU :: l) := by
  simp [escape]

set_option maxHeartbeats 1000000 in
theorem stringElem_hex {a b c d : ℕ} (ha : Model.isHex a = true) (hb : Model.isHex b = true)
    (hc : Model.isHex c = true) (hd : Model.isHex d = true) (rest : List ℕ)
    (hnl : isHighSurrogate (hexNum a b c d) = false ∨ NoLow rest) :
    stringElem (backslash :: lowerU :: a :: b :: c :: d :: rest)
      = some (hexNum a b c d, rest) := by
  have hopt : (do
      byte lowerU
      let hi ← hex4
      if isHighSurrogate hi then
        let lo ← Parser.optional lowEsc
        match lo with
        | some lo => pure (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))
        | none => pure hi
      else pure hi) (lowerU :: a :: b :: c :: d :: rest) = some (hexNum a b c d, rest) := by
    simp only [bind_apply, byte_cons_self, Option.bind_some, hex4_eq ha hb hc hd]
    rcases hnl with h | h
    · rw [if_neg (by simp [h])]
      rfl
    · by_cases hh : isHighSurrogate (hexNum a b c d) = true
      · rw [if_pos hh, bind_apply, optional_apply_of_none h]; rfl
      · rw [if_neg (by simp [hh])]; rfl
  simp only [stringElem, alt_apply, orElse_apply_of_none
    (show satisfy Specs.JSON.isUnescaped (backslash :: lowerU :: a :: b :: c :: d :: rest) = none
      by simp [unesc_backslash]),
    seqRight_apply, byte_cons_self, Option.bind_some, escape_u_chain, unicodeEscape_eq]
  exact hopt

set_option maxHeartbeats 1000000 in
theorem stringElem_pair {a b c d a' b' c' d' : ℕ}
    (ha : Model.isHex a = true) (hb : Model.isHex b = true)
    (hc : Model.isHex c = true) (hd : Model.isHex d = true)
    (ha' : Model.isHex a' = true) (hb' : Model.isHex b' = true)
    (hc' : Model.isHex c' = true) (hd' : Model.isHex d' = true)
    (hhi : isHighSurrogate (hexNum a b c d) = true)
    (hlo : isLowSurrogate (hexNum a' b' c' d') = true) (rest : List ℕ) :
    stringElem (backslash :: lowerU :: a :: b :: c :: d ::
        backslash :: lowerU :: a' :: b' :: c' :: d' :: rest)
      = some (0x10000 + (hexNum a b c d - 0xD800) * 0x400 + (hexNum a' b' c' d' - 0xDC00),
          rest) := by
  have hopt : (do
      byte lowerU
      let hi ← hex4
      if isHighSurrogate hi then
        let lo ← Parser.optional lowEsc
        match lo with
        | some lo => pure (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))
        | none => pure hi
      else pure hi) (lowerU :: a :: b :: c :: d ::
        backslash :: lowerU :: a' :: b' :: c' :: d' :: rest)
      = some (0x10000 + (hexNum a b c d - 0xD800) * 0x400 + (hexNum a' b' c' d' - 0xDC00),
          rest) := by
    simp only [bind_apply, byte_cons_self, Option.bind_some, hex4_eq ha hb hc hd]
    rw [if_pos hhi, bind_apply, optional_apply_of_some (lowEsc_pair ha' hb' hc' hd' hlo rest)]
    rfl
  simp only [stringElem, alt_apply, orElse_apply_of_none
    (show satisfy Specs.JSON.isUnescaped (backslash :: lowerU :: a :: b :: c :: d ::
        backslash :: lowerU :: a' :: b' :: c' :: d' :: rest) = none
      by simp [unesc_backslash]),
    seqRight_apply, byte_cons_self, Option.bind_some, escape_u_chain, unicodeEscape_eq]
  exact hopt

/-! ## A whole string body -/

@[simp] theorem dcpsList_nil : dcpsList [] = [] := rfl

theorem dcpsList_cons (e : SE) (l : List SE) : dcpsList (e :: l) = e.dcps ++ dcpsList l := by
  simp [dcpsList]

theorem dcps_ne_nil (e : SE) : e.dcps ≠ [] := by cases e <;> simp [SE.dcps]

theorem length_le_dcpsList : ∀ (l : List SE), l.length ≤ (dcpsList l).length := by
  intro l
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [dcpsList_cons, List.length_append, List.length_cons]
    have : 1 ≤ e.dcps.length := by
      cases hx : e.dcps with
      | nil => exact absurd hx (dcps_ne_nil e)
      | cons a t => simp
    omega

@[simp] theorem specCps_nil : specCps [] = [] := rfl
@[simp] theorem specCps_single (e : SE) : specCps [e] = [e.scp] := rfl

theorem specCps_cons2 (e e' : SE) (rest : List SE) :
    specCps (e :: e' :: rest) = if e.isHigh && e'.isLow then
      (0x10000 + (e.scp - 0xD800) * 0x400 + (e'.scp - 0xDC00)) :: specCps rest
    else e.scp :: specCps (e' :: rest) := rfl

theorem isHigh_hex {e : SE} (h : e.isHigh = true) : ∃ a b c d, e = .hex a b c d := by
  cases e <;> simp only [SE.isHigh] at h <;>
    first | exact ⟨_, _, _, _, rfl⟩ | exact absurd h (by simp)

theorem isLow_hex {e : SE} (h : e.isLow = true) : ∃ a b c d, e = .hex a b c d := by
  cases e <;> simp only [SE.isLow] at h <;>
    first | exact ⟨_, _, _, _, rfl⟩ | exact absurd h (by simp)

theorem stringElem_of_elem {e : SE} (h : e.WF) (X : List ℕ)
    (hnl : e.isHigh = false ∨ NoLow X) : stringElem (e.dcps ++ X) = some (e.scp, X) := by
  cases e with
  | plain b =>
    have hu : Model.isUnescaped b = true := h
    show stringElem (b :: X) = some (b, X)
    exact stringElem_plain hu X
  | esc b =>
    have hs : Model.isSimpleEsc b = true := h
    show stringElem (backslash :: b :: X) = some (Model.escVal b, X)
    exact stringElem_esc hs X
  | hex a b c d =>
    have h' : Model.isHex a = true ∧ Model.isHex b = true ∧ Model.isHex c = true ∧
        Model.isHex d = true := h
    show stringElem (backslash :: lowerU :: a :: b :: c :: d :: X) = some (hexNum a b c d, X)
    exact stringElem_hex h'.1 h'.2.1 h'.2.2.1 h'.2.2.2 X hnl
  | u2 b0 b1 =>
    have h' : Model.isLead2 b0 = true ∧ Model.isCont b1 = true := h
    show stringElem (((b0 - 0xC0) * 0x40 + (b1 - 0x80)) :: X)
      = some ((b0 - 0xC0) * 0x40 + (b1 - 0x80), X)
    exact stringElem_high (u2_scp_ge h') X
  | u3 b0 b1 b2 =>
    have h' : ((b0 = 0xE0 ∧ Model.isContA0BF b1 = true) ∨
        (Model.isLead3 b0 = true ∧ Model.isCont b1 = true) ∨
        (b0 = 0xED ∧ Model.isCont809F b1 = true)) ∧ Model.isCont b2 = true := h
    show stringElem (((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80)) :: X)
      = some ((b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80), X)
    exact stringElem_high (u3_scp_ge (b2 := b2) h'.1) X
  | u4 b0 b1 b2 b3 =>
    have h' : ((b0 = 0xF0 ∧ Model.isCont90BF b1 = true) ∨
        (Model.isLead4 b0 = true ∧ Model.isCont b1 = true) ∨
        (b0 = 0xF4 ∧ Model.isCont808F b1 = true)) ∧ Model.isCont b2 = true ∧
        Model.isCont b3 = true := h
    show stringElem (((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
        + (b3 - 0x80)) :: X)
      = some ((b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40 + (b3 - 0x80), X)
    exact stringElem_high (u4_scp_ge (b2 := b2) (b3 := b3) h'.1) X

theorem stringElem_of_pair {e e' : SE} (h : e.WF) (h' : e'.WF)
    (hh : e.isHigh = true) (hl : e'.isLow = true) (X : List ℕ) :
    stringElem (e.dcps ++ (e'.dcps ++ X))
      = some (0x10000 + (e.scp - 0xD800) * 0x400 + (e'.scp - 0xDC00), X) := by
  obtain ⟨a, b, c, d, rfl⟩ := isHigh_hex hh
  obtain ⟨a', b', c', d', rfl⟩ := isLow_hex hl
  have h1 : Model.isHex a = true ∧ Model.isHex b = true ∧ Model.isHex c = true ∧
      Model.isHex d = true := h
  have h2 : Model.isHex a' = true ∧ Model.isHex b' = true ∧ Model.isHex c' = true ∧
      Model.isHex d' = true := h'
  have hhi : isHighSurrogate (hexNum a b c d) = true := hh
  have hlo : isLowSurrogate (hexNum a' b' c' d') = true := hl
  show stringElem (backslash :: lowerU :: a :: b :: c :: d ::
      backslash :: lowerU :: a' :: b' :: c' :: d' :: X) = _
  exact stringElem_pair h1.1 h1.2.1 h1.2.2.1 h1.2.2.2 h2.1 h2.2.1 h2.2.2.1 h2.2.2.2 hhi hlo X

theorem many_stringElem : ∀ (n : ℕ) (l : List SE), l.length ≤ n → (∀ e ∈ l, e.WF) →
    ∀ (rest : List ℕ), stringElem rest = none → NoLow rest →
    manyUpTo n stringElem (dcpsList l ++ rest) = some (specCps l, rest) := by
  intro n
  induction n with
  | zero =>
    intro l hl _ rest _ _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp
  | succ n ih =>
    intro l hl hwf rest hstop hnolow
    match l with
    | [] =>
      simp only [dcpsList_nil, List.nil_append, specCps_nil]
      exact manyUpTo_succ_of_none hstop n
    | [e] =>
      have hstep : stringElem (e.dcps ++ rest) = some (e.scp, rest) :=
        stringElem_of_elem (hwf e (List.mem_cons_self ..)) rest (Or.inr hnolow)
      simp only [dcpsList_cons, dcpsList_nil, List.append_nil, specCps_single]
      have hz := ih [] (by simp) (by simp) rest hstop hnolow
      simp only [dcpsList_nil, List.nil_append, specCps_nil] at hz
      rw [manyUpTo_succ_of_some hstep n, hz]
      simp
    | e :: e' :: l'' =>
      have hwfe := hwf e (List.mem_cons_self ..)
      have hwfe' := hwf e' (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hwf'' : ∀ x ∈ l'', x.WF := fun x hx =>
        hwf x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      simp only [List.length_cons] at hl
      by_cases hpair : e.isHigh && e'.isLow
      · rw [Bool.and_eq_true] at hpair
        have hstep := stringElem_of_pair hwfe hwfe' hpair.1 hpair.2 (dcpsList l'' ++ rest)
        have hcps : dcpsList (e :: e' :: l'') ++ rest
            = e.dcps ++ (e'.dcps ++ (dcpsList l'' ++ rest)) := by
          rw [dcpsList_cons, dcpsList_cons]; simp [List.append_assoc]
        rw [hcps, manyUpTo_succ_of_some hstep n,
          ih l'' (by omega) hwf'' rest hstop hnolow, specCps_cons2,
          if_pos (by simp [hpair.1, hpair.2])]
        simp
      · have hnl : e.isHigh = false ∨ NoLow (dcpsList (e' :: l'') ++ rest) := by
          by_cases hh : e.isHigh = true
          · right
            have hl' : e'.isLow = false := by
              simp only [Bool.and_eq_true, not_and] at hpair
              simpa using hpair hh
            rw [dcpsList_cons, List.append_assoc]
            exact noLow_of_elem hwfe' hl' _
          · left; simpa using hh
        have hstep := stringElem_of_elem hwfe (dcpsList (e' :: l'') ++ rest) hnl
        have hcps : dcpsList (e :: e' :: l'') ++ rest
            = e.dcps ++ (dcpsList (e' :: l'') ++ rest) := by
          rw [dcpsList_cons]; simp [List.append_assoc]
        rw [hcps, manyUpTo_succ_of_some hstep n,
          ih (e' :: l'') (by simp only [List.length_cons] at *; omega)
            (fun x hx => hwf x (List.mem_cons_of_mem _ hx)) rest hstop hnolow,
          specCps_cons2, if_neg (by simpa using hpair)]
        simp

/-! ## Whitespace and strings -/

theorem isWs_eq (b : ℕ) : Model.isWs b = Specs.JSON.isWs b := rfl

/-- The next code point, if any, is not whitespace. -/
def NotWs (l : List ℕ) : Prop := ∀ c t, l = c :: t → Specs.JSON.isWs c = false

theorem notWs_cons {c : ℕ} (h : Specs.JSON.isWs c = false) (t : List ℕ) : NotWs (c :: t) := by
  intro c' t' he
  rw [List.cons.injEq] at he
  rw [← he.1]; exact h

theorem notWs_nil : NotWs [] := by intro c t h; simp at h

theorem dropWhile_ws : ∀ {w : List ℕ}, IsWs w → ∀ {rest : List ℕ}, NotWs rest →
    (w ++ rest).dropWhile Specs.JSON.isWs = rest := by
  intro w
  induction w with
  | nil =>
    intro _ rest hr
    cases rest with
    | nil => rfl
    | cons c t => rw [List.nil_append, List.dropWhile_cons, if_neg (by simp [hr c t rfl])]
  | cons b w ih =>
    intro hw rest hr
    have hb : Specs.JSON.isWs b = true := by rw [← isWs_eq]; exact hw b (List.mem_cons_self ..)
    rw [List.cons_append, List.dropWhile_cons, if_pos (by simp [hb])]
    exact ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hr

theorem ws_eq {w : List ℕ} (h : IsWs w) {rest : List ℕ} (hr : NotWs rest) :
    ws (w ++ rest) = some ((), rest) := by
  rw [ws, skipWhile_apply, dropWhile_ws h hr]

theorem stringElem_quote (rest : List ℕ) : stringElem (quote :: rest) = none := by
  simp [stringElem, show Specs.JSON.isUnescaped quote = false from by decide]

theorem noLow_quote (rest : List ℕ) : NoLow (quote :: rest) :=
  noLow_of_head (by decide) rest

theorem string_eq {body : List SE} (h : ∀ e ∈ body, e.WF) (rest : List ℕ) :
    string (quote :: (dcpsList body ++ (quote :: rest))) = some (specCps body, rest) := by
  set X : List ℕ := dcpsList body ++ (quote :: rest) with hX
  have hlen : body.length ≤ X.length := by
    rw [hX, List.length_append]
    have := length_le_dcpsList body
    omega
  have hmany : manyUpTo X.length stringElem X = some (specCps body, quote :: rest) := by
    rw [hX]
    exact many_stringElem X.length body hlen h (quote :: rest) (stringElem_quote rest)
      (noLow_quote rest)
  show ((byte quote *> many stringElem) <* byte quote) (quote :: X) = _
  rw [seqLeft_apply, seqRight_apply, byte_cons_self]
  simp only [Option.bind_some, many_apply, hmany, byte_cons_self]
  rfl

/-! ## Digit runs -/

theorem takeDrop_append {q : ℕ → Bool} : ∀ {l : List ℕ}, (∀ x ∈ l, q x = true) →
    ∀ {rest : List ℕ}, (∀ c t, rest = c :: t → q c = false) →
      (l ++ rest).takeWhile q = l ∧ (l ++ rest).dropWhile q = rest := by
  intro l
  induction l with
  | nil =>
    intro _ rest hr
    cases rest with
    | nil => exact ⟨rfl, rfl⟩
    | cons c t =>
      refine ⟨?_, ?_⟩
      · rw [List.nil_append, List.takeWhile_cons, if_neg (by simp [hr c t rfl])]
      · rw [List.nil_append, List.dropWhile_cons, if_neg (by simp [hr c t rfl])]
  | cons b l ih =>
    intro hl rest hr
    have hb : q b = true := hl b (List.mem_cons_self ..)
    obtain ⟨i1, i2⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hr
    refine ⟨?_, ?_⟩
    · rw [List.cons_append, List.takeWhile_cons, if_pos (by simp [hb]), i1]
    · rw [List.cons_append, List.dropWhile_cons, if_pos (by simp [hb]), i2]

theorem drop_takeWhile_length : ∀ (q : ℕ → Bool) (l : List ℕ),
    l.drop (l.takeWhile q).length = l.dropWhile q := by
  intro q l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.takeWhile_cons, List.dropWhile_cons]
    by_cases h : q b = true
    · simp only [h, if_true, List.length_cons, List.drop_succ_cons]
      exact ih
    · simp only [h, Bool.false_eq_true, if_false, List.length_nil, List.drop_zero]

theorem many_satisfy (q : ℕ → Bool) (l : List ℕ) :
    many (satisfy q) l = some (l.takeWhile q, l.dropWhile q) := by
  rw [many_apply, manyUpTo_satisfy]
  have h1 : (l.takeWhile q).length ≤ l.length := by
    have := List.takeWhile_append_dropWhile (l := l) (p := q)
    have := congrArg List.length this
    simp only [List.length_append] at this
    omega
  rw [List.take_of_length_le h1, Nat.min_eq_right h1, drop_takeWhile_length]

theorem digitsOf_isDigit {ds : List ℕ} (h : ∀ x ∈ ds, x ≤ 9) :
    ∀ x ∈ digitsOf ds, Specs.JSON.isDigit x = true := by
  intro x hx
  simp only [digitsOf, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have := h y hy
  simp only [Specs.JSON.isDigit, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · show (0x30 : ℕ) ≤ y + 0x30; omega
  · show y + 0x30 ≤ 0x39; omega

theorem digitValue_map {ds : List ℕ} : (digitsOf ds).map digitValue = ds := by
  simp only [digitsOf, List.map_map]
  rw [show (digitValue ∘ fun x => x + digit0) = id from by
    funext x; simp only [Function.comp_apply, digitValue, id]; show x + 0x30 - 0x30 = x; omega]
  simp

/-- The rest of the input does not continue a number. -/
def NotNum (l : List ℕ) : Prop :=
  ∀ c t, l = c :: t → Specs.JSON.isDigit c = false ∧ c ≠ dot ∧ c ≠ lowerE ∧ c ≠ upperE

theorem notDigit_of_notNum {l : List ℕ} (h : NotNum l) :
    ∀ c t, l = c :: t → Specs.JSON.isDigit c = false := fun c t he => (h c t he).1

theorem digitValue_add (d : ℕ) : digitValue (d + digit0) = d := by
  simp only [digitValue]
  show d + 0x30 - 0x30 = d
  omega

theorem digits1_eq {ds : List ℕ} (hne : ds ≠ []) (hd : ∀ x ∈ ds, x ≤ 9) {rest : List ℕ}
    (hr : ∀ c t, rest = c :: t → Specs.JSON.isDigit c = false) :
    digits1 (digitsOf ds ++ rest) = some (ds, rest) := by
  obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
    cases hx : ds with
    | nil => exact absurd hx hne
    | cons d ds' => exact ⟨d, ds', rfl⟩
  have hd9 : d ≤ 9 := hd d (List.mem_cons_self ..)
  have hdd : ∀ x ∈ ds', x ≤ 9 := fun x hx => hd x (List.mem_cons_of_mem _ hx)
  have hdig : Specs.JSON.isDigit (d + digit0) = true := by
    simp only [Specs.JSON.isDigit, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by show (0x30:ℕ) ≤ d + 0x30; omega, by show d + 0x30 ≤ 0x39; omega⟩
  obtain ⟨ht, hdw⟩ := takeDrop_append (q := Specs.JSON.isDigit) (digitsOf_isDigit hdd) hr
  have hsplit : digitsOf (d :: ds') ++ rest = (d + digit0) :: (digitsOf ds' ++ rest) := by
    simp [digitsOf]
  show (do let a ← satisfy Specs.JSON.isDigit
           let as ← many (satisfy Specs.JSON.isDigit)
           pure ((a :: as).map digitValue)) (digitsOf (d :: ds') ++ rest) = _
  rw [hsplit]
  simp only [bind_apply, satisfy_cons, hdig, if_true, Option.bind_some, many_satisfy, ht, hdw,
    pure_apply, Option.some.injEq, Prod.mk.injEq, and_true, List.map_cons, digitValue_add,
    digitValue_map]

theorem intDigits_eq {ints : List ℕ}
    (hwf : ints = [0] ∨ (∃ d ds, ints = d :: ds ∧ 1 ≤ d ∧ d ≤ 9 ∧ ∀ x ∈ ds, x ≤ 9))
    {rest : List ℕ} (hr : ∀ c t, rest = c :: t → Specs.JSON.isDigit c = false) :
    intDigits (digitsOf ints ++ rest) = some (ints, rest) := by
  rcases hwf with rfl | ⟨d, ds, rfl, hd1, hd9, hds⟩
  · have h1 : digitsOf [0] ++ rest = digit0 :: rest := by simp [digitsOf]
    have hfst : (byte digit0 *> notFollowedBy Specs.JSON.isDigit *> pure [0])
        (digit0 :: rest) = some ([0], rest) := by
      simp only [seqRight_apply, byte_cons_self, Option.bind_some]
      cases hx : rest with
      | nil => rfl
      | cons c t => rw [notFollowedBy_cons, if_neg (by simp [hr c t hx])]; rfl
    show ((byte digit0 *> notFollowedBy Specs.JSON.isDigit *> pure [0]) <|> _)
      (digitsOf [0] ++ rest) = _
    rw [h1, alt_apply, orElse_apply_of_some hfst]
  · have hdig : Specs.JSON.isDigitNz (d + digit0) = true := by
      simp only [Specs.JSON.isDigitNz, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by show (0x30:ℕ) < d + 0x30; omega, by show d + 0x30 ≤ 0x39; omega⟩
    have hne0 : ¬ (d + digit0 = digit0) := by show ¬ (d + 0x30 = 0x30); omega
    obtain ⟨ht, hdw⟩ := takeDrop_append (q := Specs.JSON.isDigit) (digitsOf_isDigit hds) hr
    have h1 : digitsOf (d :: ds) ++ rest = (d + digit0) :: (digitsOf ds ++ rest) := by
      simp [digitsOf]
    have hfst : (byte digit0 *> notFollowedBy Specs.JSON.isDigit *> pure [0])
        ((d + digit0) :: (digitsOf ds ++ rest)) = none := by
      simp only [seqRight_apply, byte_cons, if_neg hne0]
      rfl
    show ((byte digit0 *> notFollowedBy Specs.JSON.isDigit *> pure [0]) <|>
      (do let a ← satisfy Specs.JSON.isDigitNz
          let as ← many (satisfy Specs.JSON.isDigit)
          pure ((a :: as).map digitValue))) (digitsOf (d :: ds) ++ rest) = _
    rw [h1, alt_apply, orElse_apply_of_none hfst]
    simp only [bind_apply, satisfy_cons, hdig, if_true, Option.bind_some, many_satisfy, ht, hdw,
      pure_apply, Option.some.injEq, Prod.mk.injEq, and_true, List.map_cons, digitValue_add,
      digitValue_map]

/-! ## Numbers -/

def fracPart (nm : SNum) : List ℕ := if nm.frac = [] then [] else dot :: digitsOf nm.frac
def expPart (nm : SNum) : List ℕ := (nm.exp.map SExp.bytes).getD []

theorem snum_bytes_eq (nm : SNum) :
    nm.bytes = (if nm.neg then [minus] else [])
      ++ (digitsOf nm.ints ++ (fracPart nm ++ expPart nm)) := by
  rw [SNum.bytes, fracPart, expPart, digitsOf]
  cases nm.exp <;> simp [List.append_assoc, digitsOf]

theorem letter_not_digit {c : ℕ} (h : c = lowerE ∨ c = upperE) :
    Specs.JSON.isDigit c = false := by rcases h with rfl | rfl <;> decide

theorem exponent_eq {e : SExp} (hl : e.letter = lowerE ∨ e.letter = upperE)
    (hs : match e.sign with | none => True | some sg => sg = plus ∨ sg = minus)
    (hne : e.digits ≠ []) (hd : ∀ x ∈ e.digits, x ≤ 9)
    {rest : List ℕ} (hr : ∀ c t, rest = c :: t → Specs.JSON.isDigit c = false) :
    exponent (SExp.bytes e ++ rest)
      = some ((decide (e.sign = some minus), e.digits), rest) := by
  have hdigits : digits1 (digitsOf e.digits ++ rest) = some (e.digits, rest) :=
    digits1_eq hne hd hr
  have hletter : ∀ (X : List ℕ), (byte lowerE <|> byte upperE) (e.letter :: X)
      = some ((), X) := by
    intro X
    rcases hl with h | h <;> rw [h, alt_apply]
    · exact orElse_apply_of_some (byte_cons_self _ _) _
    · rw [orElse_apply_of_none (by rw [byte_cons, if_neg (by decide)]) _]
      exact byte_cons_self _ _
  cases hsn : e.sign with
  | none =>
    have hsplit : SExp.bytes e ++ rest = e.letter :: (digitsOf e.digits ++ rest) := by
      simp [SExp.bytes, hsn, digitsOf]
    obtain ⟨d, ds, hds⟩ : ∃ d ds, e.digits = d :: ds := by
      cases hx : e.digits with
      | nil => exact absurd hx hne
      | cons d ds => exact ⟨d, ds, rfl⟩
    have hd9 : d ≤ 9 := hd d (by rw [hds]; exact List.mem_cons_self ..)
    have hhead : digitsOf e.digits ++ rest = (d + digit0) :: (digitsOf ds ++ rest) := by
      rw [hds]; simp [digitsOf]
    show (do (byte lowerE <|> byte upperE)
             let neg ← ((byte plus *> pure false) <|> (byte minus *> pure true) <|> pure false)
             let ds ← digits1
             pure (neg, ds)) (SExp.bytes e ++ rest) = _
    rw [hsplit]
    simp only [seqRight_apply, hletter, Option.bind_some, bind_apply]
    rw [hhead]
    have hp : (byte plus *> pure false) ((d + digit0) :: (digitsOf ds ++ rest)) = none := by
      simp only [seqRight_apply, byte_cons, if_neg (show ¬ (d + digit0 = plus) from by
        show ¬ (d + 0x30 = 0x2B); omega)]
      rfl
    have hm : (byte minus *> pure true) ((d + digit0) :: (digitsOf ds ++ rest)) = none := by
      simp only [seqRight_apply, byte_cons, if_neg (show ¬ (d + digit0 = minus) from by
        show ¬ (d + 0x30 = 0x2D); omega)]
      rfl
    rw [alt_apply, orElse_apply_of_none hp, alt_apply, orElse_apply_of_none hm, pure_apply]
    simp only [Option.bind_some]
    rw [← hhead, hdigits]
    simp
  | some sg =>
    have hsplit : SExp.bytes e ++ rest
        = e.letter :: (sg :: (digitsOf e.digits ++ rest)) := by
      simp [SExp.bytes, hsn, digitsOf]
    rw [hsn] at hs
    show (do (byte lowerE <|> byte upperE)
             let neg ← ((byte plus *> pure false) <|> (byte minus *> pure true) <|> pure false)
             let ds ← digits1
             pure (neg, ds)) (SExp.bytes e ++ rest) = _
    rw [hsplit]
    simp only [seqRight_apply, hletter, Option.bind_some, bind_apply]
    rcases hs with rfl | rfl
    · rw [alt_apply, orElse_apply_of_some (show (byte plus *> pure false)
        (plus :: (digitsOf e.digits ++ rest)) = some (false, digitsOf e.digits ++ rest) from by
        simp only [seqRight_apply, byte_cons_self]; rfl)]
      simp only [Option.bind_some]
      rw [hdigits]
      simp
    · rw [alt_apply, orElse_apply_of_none (show (byte plus *> pure false)
        (minus :: (digitsOf e.digits ++ rest)) = none from by
        simp only [seqRight_apply, byte_cons, if_neg (show ¬ (minus = plus) from by decide)]
        rfl), alt_apply,
        orElse_apply_of_some (show (byte minus *> pure true)
        (minus :: (digitsOf e.digits ++ rest)) = some (true, digitsOf e.digits ++ rest) from by
        simp only [seqRight_apply, byte_cons_self]; rfl)]
      simp only [Option.bind_some]
      rw [hdigits]
      simp

theorem dotDigits_none {Z : List ℕ} (h : ∀ c t, Z = c :: t → ¬ (c = dot)) :
    (byte dot *> digits1) Z = none := by
  cases Z with
  | nil => rfl
  | cons c t => simp only [seqRight_apply, byte_cons, if_neg (h c t rfl)]; rfl

theorem exponent_none {Z : List ℕ}
    (h : ∀ c t, Z = c :: t → ¬ (c = lowerE) ∧ ¬ (c = upperE)) : exponent Z = none := by
  show (do (byte lowerE <|> byte upperE)
           let neg ← ((byte plus *> pure false) <|> (byte minus *> pure true) <|> pure false)
           let ds ← digits1
           pure (neg, ds)) Z = none
  cases Z with
  | nil => rfl
  | cons c t =>
    obtain ⟨h1, h2⟩ := h c t rfl
    have hfail : (byte lowerE <|> byte upperE) (c :: t) = none := by
      rw [alt_apply, orElse_apply_of_none (show byte lowerE (c :: t) = none from by
        rw [byte_cons, if_neg h1]), byte_cons, if_neg h2]
    rw [bind_apply, hfail]
    rfl

theorem snum_bytes_append (nm : SNum) (rest : List ℕ) :
    nm.bytes ++ rest = (if nm.neg then [minus] else [])
      ++ (digitsOf nm.ints ++ (fracPart nm ++ (expPart nm ++ rest))) := by
  rw [snum_bytes_eq]; simp [List.append_assoc]

/-- The `JNumber` a serialized number denotes. -/
def jnumOf (nm : SNum) : JNumber :=
  { negative := nm.neg, intDigits := nm.ints, fracDigits := nm.frac,
    expNegative := (nm.exp.map fun e => decide (e.sign = some minus)).getD false,
    expDigits := (nm.exp.map (·.digits)).getD [] }

set_option maxHeartbeats 1000000 in
theorem number_eq {nm : SNum} (h : nm.WF) {rest : List ℕ} (hr : NotNum rest) :
    number (nm.bytes ++ rest) = some (jnumOf nm, rest) := by
  obtain ⟨hints, hfrac, hexp⟩ := h
  -- the tail after the exponent
  have hZ : ∀ c t, expPart nm ++ rest = c :: t →
      Specs.JSON.isDigit c = false ∧ ¬ (c = dot) := by
    intro c t he
    cases hx : nm.exp with
    | none =>
      rw [expPart, hx] at he
      simp only [Option.map_none, Option.getD_none, List.nil_append] at he
      obtain ⟨h1, h2, _, _⟩ := hr c t he
      exact ⟨h1, h2⟩
    | some e =>
      rw [hx] at hexp
      obtain ⟨hl, _, _, _⟩ := hexp
      rw [expPart, hx] at he
      simp only [Option.map_some, Option.getD_some, SExp.bytes, List.cons_append,
        List.cons.injEq] at he
      rw [← he.1]
      exact ⟨letter_not_digit hl, by rcases hl with h1 | h1 <;> rw [h1] <;> decide⟩
  have hY : ∀ c t, fracPart nm ++ (expPart nm ++ rest) = c :: t →
      Specs.JSON.isDigit c = false := by
    intro c t he
    by_cases hf : nm.frac = []
    · rw [fracPart, if_pos hf, List.nil_append] at he
      exact (hZ c t he).1
    · rw [fracPart, if_neg hf, List.cons_append, List.cons.injEq] at he
      rw [← he.1]; decide
  have hintsne : ∃ d ds, nm.ints = d :: ds ∧ d ≤ 9 := by
    rcases hints with h1 | ⟨d, ds, h1, _, h2, _⟩
    · exact ⟨0, [], h1, by omega⟩
    · exact ⟨d, ds, h1, h2⟩
  obtain ⟨d0, ds0, hints0, hd09⟩ := hintsne
  set Y : List ℕ := digitsOf nm.ints ++ (fracPart nm ++ (expPart nm ++ rest)) with hYdef
  have hYhead : Y = (d0 + digit0) :: (digitsOf ds0 ++ (fracPart nm ++ (expPart nm ++ rest))) := by
    rw [hYdef, hints0]; simp [digitsOf]
  -- stage 1: the sign
  have hs1 : Parser.optional (byte minus) ((if nm.neg then [minus] else []) ++ Y)
      = some (if nm.neg then some () else none, Y) := by
    by_cases hn : nm.neg
    · rw [if_pos hn, if_pos hn, List.cons_append, List.nil_append]
      exact optional_apply_of_some (byte_cons_self _ _)
    · rw [if_neg hn, if_neg hn, List.nil_append]
      refine optional_apply_of_none ?_
      rw [hYhead, byte_cons, if_neg (show ¬ (d0 + digit0 = minus) from by
        show ¬ (d0 + 0x30 = 0x2D); omega)]
  -- stage 2: the integer part
  have hs2 : intDigits Y = some (nm.ints, fracPart nm ++ (expPart nm ++ rest)) :=
    intDigits_eq hints hY
  -- stage 3: the fractional part
  have hs3 : Parser.optional (byte dot *> digits1) (fracPart nm ++ (expPart nm ++ rest))
      = some (if nm.frac = [] then none else some nm.frac, expPart nm ++ rest) := by
    by_cases hf : nm.frac = []
    · rw [if_pos hf, fracPart, if_pos hf, List.nil_append]
      exact optional_apply_of_none (dotDigits_none fun c t he => (hZ c t he).2)
    · rw [if_neg hf, fracPart, if_neg hf, List.cons_append]
      refine optional_apply_of_some ?_
      simp only [seqRight_apply, byte_cons_self, Option.bind_some]
      exact digits1_eq hf hfrac fun c t he => (hZ c t he).1
  -- stage 4: the exponent
  have hs4 : Parser.optional exponent (expPart nm ++ rest)
      = some (nm.exp.map fun e => (decide (e.sign = some minus), e.digits), rest) := by
    cases hx : nm.exp with
    | none =>
      rw [expPart, hx]
      simp only [Option.map_none, Option.getD_none, List.nil_append]
      exact optional_apply_of_none (exponent_none fun c t he =>
        ⟨(hr c t he).2.2.1, (hr c t he).2.2.2⟩)
    | some e =>
      rw [hx] at hexp
      obtain ⟨hl, hsg, hne, hdg⟩ := hexp
      rw [expPart, hx]
      simp only [Option.map_some, Option.getD_some]
      exact optional_apply_of_some
        (exponent_eq hl hsg hne hdg fun c t he => (hr c t he).1)
  rw [snum_bytes_append, number]
  rw [bind_apply, hs1]
  simp only [Option.bind_some]
  rw [bind_apply, hs2]
  simp only [Option.bind_some]
  rw [bind_apply, hs3]
  simp only [Option.bind_some]
  rw [bind_apply, hs4]
  simp only [Option.bind_some, pure_apply, Option.some.injEq, Prod.mk.injEq, and_true]
  rw [jnumOf]
  by_cases hn : nm.neg <;> by_cases hf : nm.frac = [] <;>
    cases hx : nm.exp <;> simp [hn, hf, hx]

/-! ## Failing alternatives -/

theorem object_none {f : ℕ} {l : List ℕ} (h : ∀ c t, l = c :: t → ¬ (c = lbrace)) :
    object f l = none := by
  rw [object]
  cases l with
  | nil => rfl
  | cons c t => simp only [seqLeft_apply, seqRight_apply, byte_cons, if_neg (h c t rfl)]; rfl

theorem array_none {f : ℕ} {l : List ℕ} (h : ∀ c t, l = c :: t → ¬ (c = lbracket)) :
    array f l = none := by
  rw [array]
  cases l with
  | nil => rfl
  | cons c t => simp only [seqLeft_apply, seqRight_apply, byte_cons, if_neg (h c t rfl)]; rfl

theorem string_none {l : List ℕ} (h : ∀ c t, l = c :: t → ¬ (c = quote)) : string l = none := by
  show ((byte quote *> many stringElem) <* byte quote) l = none
  cases l with
  | nil => rfl
  | cons c t => simp only [seqLeft_apply, seqRight_apply, byte_cons, if_neg (h c t rfl)]; rfl

theorem literal_none_head {b : ℕ} {bs : List ℕ} {l : List ℕ}
    (h : ∀ c t, l = c :: t → ¬ (c = b)) : literal (b :: bs) l = none := by
  cases l with
  | nil => rw [literal_cons]; rfl
  | cons c t => exact literal_cons_of_ne (h c t rfl)

theorem literal_append : ∀ (bs rest : List ℕ), literal bs (bs ++ rest) = some ((), rest) := by
  intro bs
  induction bs with
  | nil => intro rest; rfl
  | cons b bs ih => intro rest; rw [List.cons_append, literal_cons, byte_cons_self]; exact ih rest

/-! ## The head of a serialized value -/

theorem snum_head {nm : SNum} (h : nm.WF) : ∃ c t, nm.bytes = c :: t ∧
    ¬ (c = lbrace) ∧ ¬ (c = lbracket) ∧ ¬ (c = quote) ∧ ¬ (c = lowerT) ∧ ¬ (c = lowerF) ∧
    ¬ (c = lowerN) ∧ Specs.JSON.isWs c = false := by
  obtain ⟨hints, _, _⟩ := h
  obtain ⟨d, ds, hd, hd9⟩ : ∃ d ds, nm.ints = d :: ds ∧ d ≤ 9 := by
    rcases hints with h1 | ⟨d, ds, h1, _, h2, _⟩
    · exact ⟨0, [], h1, by omega⟩
    · exact ⟨d, ds, h1, h2⟩
  by_cases hn : nm.neg
  · refine ⟨minus, (digitsOf nm.ints ++ (fracPart nm ++ expPart nm)), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;>
      first
        | (rw [snum_bytes_eq, if_pos hn]; rfl)
        | decide
  · refine ⟨d + digit0, (digitsOf ds ++ (fracPart nm ++ expPart nm)), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · rw [snum_bytes_eq, if_neg hn, hd]; simp [digitsOf]
    · show ¬ (d + 0x30 = 0x7B); omega
    · show ¬ (d + 0x30 = 0x5B); omega
    · show ¬ (d + 0x30 = 0x22); omega
    · show ¬ (d + 0x30 = 0x74); omega
    · show ¬ (d + 0x30 = 0x66); omega
    · show ¬ (d + 0x30 = 0x6E); omega
    · simp only [Specs.JSON.isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
        [show ¬ (d + 0x30 = 0x20); show ¬ (d + 0x30 = 0x09); show ¬ (d + 0x30 = 0x0A);
         show ¬ (d + 0x30 = 0x0D)] <;> omega

theorem obj_none_cons {f c : ℕ} {t : List ℕ} (h : ¬ (c = lbrace)) :
    (JSON.obj <$> object f) (c :: t) = none := by
  rw [map_apply, object_none (fun c' t' he => by cases he; exact h)]; rfl

theorem arr_none_cons {f c : ℕ} {t : List ℕ} (h : ¬ (c = lbracket)) :
    (JSON.arr <$> array f) (c :: t) = none := by
  rw [map_apply, array_none (fun c' t' he => by cases he; exact h)]; rfl

theorem str_none_cons {c : ℕ} {t : List ℕ} (h : ¬ (c = quote)) :
    (JSON.str <$> string) (c :: t) = none := by
  rw [map_apply, string_none (fun c' t' he => by cases he; exact h)]; rfl

theorem lit_none_cons {b c : ℕ} {bs t : List ℕ} (a : JSON) (h : ¬ (c = b)) :
    (literal (b :: bs) *> pure a) (c :: t) = none := by
  rw [seqRight_apply, literal_none_head (fun c' t' he => by cases he; exact h)]; rfl

theorem lit_some {bs rest : List ℕ} (a : JSON) :
    (literal bs *> pure a) (bs ++ rest) = some (a, rest) := by
  rw [seqRight_apply, literal_append]; rfl

set_option maxHeartbeats 1000000 in
theorem value_eq {v : SV} (hwf : v.WF) (f : ℕ) {w : List ℕ} (hw : IsWs w) {rest : List ℕ}
    (hr : NotNum rest) :
    value (f + 1) (w ++ (SV.cps v ++ rest)) = some (SV.json v, rest) := by
  cases v with
  | str body =>
    have hcps : SV.cps (SV.str body) ++ rest = quote :: (dcpsList body ++ (quote :: rest)) := by
      simp [SV.cps, List.append_assoc]
    rw [hcps, value, seqRight_apply,
      ws_eq hw (notWs_cons (show Specs.JSON.isWs quote = false by decide) _)]
    simp only [Option.bind_some]
    rw [alt_apply, orElse_apply_of_none (obj_none_cons (by decide)),
      alt_apply, orElse_apply_of_none (arr_none_cons (by decide)),
      alt_apply, orElse_apply_of_some
        (show (JSON.str <$> string) (quote :: (dcpsList body ++ (quote :: rest)))
          = some (JSON.str (specCps body), rest) by
          rw [map_apply, string_eq hwf rest]; rfl)]
    rfl
  | num nm =>
    obtain ⟨c, t, hct, h1, h2, h3, h4, h5, h6, h7⟩ := snum_head hwf
    have hcps : SV.cps (SV.num nm) ++ rest = c :: (t ++ rest) := by
      rw [show SV.cps (SV.num nm) = nm.bytes from rfl, hct]; rfl
    rw [hcps, value, seqRight_apply, ws_eq hw (notWs_cons h7 _)]
    simp only [Option.bind_some]
    rw [alt_apply, orElse_apply_of_none (obj_none_cons h1),
      alt_apply, orElse_apply_of_none (arr_none_cons h2),
      alt_apply, orElse_apply_of_none (str_none_cons h3),
      alt_apply, orElse_apply_of_none (lit_none_cons _ h4),
      alt_apply, orElse_apply_of_none (lit_none_cons _ h5),
      alt_apply, orElse_apply_of_none (lit_none_cons _ h6),
      map_apply, show c :: (t ++ rest) = nm.bytes ++ rest from by rw [hct]; rfl,
      number_eq hwf hr]
    rfl
  | btrue =>
    have hcps : SV.cps SV.btrue ++ rest = lowerT :: (lowerR :: lowerU :: lowerE :: rest) := by
      rfl
    rw [hcps, value, seqRight_apply,
      ws_eq hw (notWs_cons (show Specs.JSON.isWs lowerT = false by decide) _)]
    simp only [Option.bind_some]
    rw [alt_apply, orElse_apply_of_none (obj_none_cons (by decide)),
      alt_apply, orElse_apply_of_none (arr_none_cons (by decide)),
      alt_apply, orElse_apply_of_none (str_none_cons (by decide)),
      alt_apply, orElse_apply_of_some
        (show (literal trueLit *> pure (JSON.bool true))
            (lowerT :: (lowerR :: lowerU :: lowerE :: rest))
          = some (JSON.bool true, rest) from lit_some _)]
    rfl
  | bfalse =>
    have hcps : SV.cps SV.bfalse ++ rest
        = lowerF :: (lowerA :: 0x6C :: 0x73 :: lowerE :: rest) := by rfl
    rw [hcps, value, seqRight_apply,
      ws_eq hw (notWs_cons (show Specs.JSON.isWs lowerF = false by decide) _)]
    simp only [Option.bind_some]
    rw [alt_apply, orElse_apply_of_none (obj_none_cons (by decide)),
      alt_apply, orElse_apply_of_none (arr_none_cons (by decide)),
      alt_apply, orElse_apply_of_none (str_none_cons (by decide)),
      alt_apply, orElse_apply_of_none (lit_none_cons _ (by decide)),
      alt_apply, orElse_apply_of_some
        (show (literal falseLit *> pure (JSON.bool false))
            (lowerF :: (lowerA :: 0x6C :: 0x73 :: lowerE :: rest))
          = some (JSON.bool false, rest) from lit_some _)]
    rfl
  | null =>
    have hcps : SV.cps SV.null ++ rest = lowerN :: (lowerU :: 0x6C :: 0x6C :: rest) := by rfl
    rw [hcps, value, seqRight_apply,
      ws_eq hw (notWs_cons (show Specs.JSON.isWs lowerN = false by decide) _)]
    simp only [Option.bind_some]
    rw [alt_apply, orElse_apply_of_none (obj_none_cons (by decide)),
      alt_apply, orElse_apply_of_none (arr_none_cons (by decide)),
      alt_apply, orElse_apply_of_none (str_none_cons (by decide)),
      alt_apply, orElse_apply_of_none (lit_none_cons _ (by decide)),
      alt_apply, orElse_apply_of_none (lit_none_cons _ (by decide)),
      alt_apply, orElse_apply_of_some
        (show (literal nullLit *> pure JSON.null) (lowerN :: (lowerU :: 0x6C :: 0x6C :: rest))
          = some (JSON.null, rest) from lit_some _)]
    rfl

/-! ## Members -/

theorem notNum_ws {c : ℕ} (h : Model.isWs c = true) :
    Specs.JSON.isDigit c = false ∧ ¬ (c = dot) ∧ ¬ (c = lowerE) ∧ ¬ (c = upperE) := by
  simp only [Model.isWs, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h1 | h1) | h1) | h1 <;> subst h1 <;> exact ⟨by decide, by decide, by decide,
    by decide⟩

theorem notNum_of_ws {w : List ℕ} (hw : IsWs w) {X : List ℕ} (hX : NotNum X) :
    NotNum (w ++ X) := by
  cases w with
  | nil => simpa using hX
  | cons c t =>
    intro c' t' he
    rw [List.cons_append, List.cons.injEq] at he
    rw [← he.1]
    exact notNum_ws (hw c (List.mem_cons_self ..))

theorem notNum_comma (X : List ℕ) : NotNum (comma :: X) := by
  intro c t he
  rw [List.cons.injEq] at he
  rw [← he.1]
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem notNum_rbrace (X : List ℕ) : NotNum (rbrace :: X) := by
  intro c t he
  rw [List.cons.injEq] at he
  rw [← he.1]
  exact ⟨by decide, by decide, by decide, by decide⟩

theorem member_eq {m : SMem} (h : m.WF) (f : ℕ) {rest : List ℕ} (hr : NotNum rest) :
    member (f + 1) (SMem.cpsNoWs3 m ++ rest)
      = some ((specCps m.key, SV.json m.val), rest) := by
  obtain ⟨hws0, hws1, hws2, hws3, hkey, hvwf, _⟩ := h
  have hsplit : SMem.cpsNoWs3 m ++ rest
      = m.ws0 ++ (quote :: (dcpsList m.key ++ (quote :: (m.ws1 ++
          (colon :: (m.ws2 ++ (SV.cps m.val ++ rest))))))) := by
    simp [SMem.cpsNoWs3, List.append_assoc]
  rw [member, hsplit, bind_apply,
    ws_eq hws0 (notWs_cons (show Specs.JSON.isWs quote = false by decide) _)]
  simp only [Option.bind_some, bind_apply]
  rw [string_eq hkey (m.ws1 ++ (colon :: (m.ws2 ++ (SV.cps m.val ++ rest))))]
  simp only [Option.bind_some, bind_apply, seqRight_apply]
  rw [ws_eq hws1 (notWs_cons (show Specs.JSON.isWs colon = false by decide) _)]
  simp only [Option.bind_some, byte_cons_self]
  rw [value_eq hvwf f hws2 hr]
  rfl

/-! ## Length bounds -/

theorem cpsNoWs3_ne_nil (m : SMem) : SMem.cpsNoWs3 m ≠ [] := by
  intro he
  have : (SMem.cpsNoWs3 m).length = 0 := by rw [he]; rfl
  rw [SMem.cpsNoWs3] at this
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

theorem length_flatten_members : ∀ (ms : List SMem),
    ms.length ≤ ((ms.map fun m' => comma :: SMem.cps m').flatten).length := by
  intro ms
  induction ms with
  | nil => simp
  | cons m ms ih => simp only [List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons]; omega

theorem notNum_flatten_rbrace (ms : List SMem) (post : List ℕ) :
    NotNum ((ms.map fun m' => comma :: SMem.cps m').flatten ++ (rbrace :: post)) := by
  cases ms with
  | nil => simpa using notNum_rbrace post
  | cons m ms =>
    simp only [List.map_cons, List.flatten_cons, List.cons_append]
    exact notNum_comma _

set_option maxHeartbeats 1000000 in
theorem many_members : ∀ (n : ℕ) (ms : List SMem), ms.length ≤ n → (∀ m ∈ ms, m.WF) →
    ∀ (F : ℕ) (wsPrev : List ℕ), IsWs wsPrev → ∀ (post : List ℕ),
      ∃ wsLast, IsWs wsLast ∧
        manyUpTo n ((ws *> byte comma) *> member (F + 1))
          (wsPrev ++ ((ms.map fun m' => comma :: SMem.cps m').flatten ++ (rbrace :: post)))
          = some (ms.map fun m' => (specCps m'.key, SV.json m'.val),
              wsLast ++ (rbrace :: post)) := by
  intro n
  induction n with
  | zero =>
    intro ms hlen hms F wsPrev hws post
    have hnil : ms = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    exact ⟨wsPrev, hws, by simp⟩
  | succ n ih =>
    intro ms hlen hms F wsPrev hws post
    cases ms with
    | nil =>
      refine ⟨wsPrev, hws, ?_⟩
      simp only [List.map_nil, List.flatten_nil, List.nil_append]
      refine manyUpTo_succ_of_none ?_ n
      rw [seqRight_apply, seqRight_apply,
        ws_eq hws (notWs_cons (show Specs.JSON.isWs rbrace = false by decide) _)]
      simp only [Option.bind_some, byte_cons, if_neg (show ¬ (rbrace = comma) by decide)]
      rfl
    | cons m ms =>
      have hsplit : wsPrev ++ (((m :: ms).map fun m' => comma :: SMem.cps m').flatten
            ++ (rbrace :: post))
          = wsPrev ++ (comma :: (SMem.cpsNoWs3 m ++ (m.ws3 ++
              ((ms.map fun m' => comma :: SMem.cps m').flatten ++ (rbrace :: post))))) := by
        simp [SMem.cps, List.append_assoc]
      have hmwf := hms m (List.mem_cons_self ..)
      have hstep : ((ws *> byte comma) *> member (F + 1))
          (wsPrev ++ (comma :: (SMem.cpsNoWs3 m ++ (m.ws3 ++
            ((ms.map fun m' => comma :: SMem.cps m').flatten ++ (rbrace :: post))))))
          = some ((specCps m.key, SV.json m.val),
              m.ws3 ++ ((ms.map fun m' => comma :: SMem.cps m').flatten ++ (rbrace :: post))) := by
        rw [seqRight_apply, seqRight_apply,
          ws_eq hws (notWs_cons (show Specs.JSON.isWs comma = false by decide) _)]
        simp only [Option.bind_some, byte_cons_self]
        exact member_eq hmwf F (notNum_of_ws hmwf.2.2.2.1 (notNum_flatten_rbrace ms post))
      obtain ⟨wsLast, hwsLast, hrec⟩ := ih ms (by simp only [List.length_cons] at hlen; omega)
        (fun x hx => hms x (List.mem_cons_of_mem _ hx)) F m.ws3 hmwf.2.2.2.1 post
      refine ⟨wsLast, hwsLast, ?_⟩
      rw [hsplit, manyUpTo_succ_of_some hstep n, hrec]
      simp

set_option maxHeartbeats 1000000 in
theorem object_eq {ms : List SMem} (hms : ∀ m ∈ ms, m.WF) {we : List ℕ} (hwe : IsWs we)
    (F : ℕ) (hlen : ms.length ≤ F) {post : List ℕ} :
    object (F + 1) (lbrace :: (bodyCps ms we ++ (rbrace :: post)))
      = some (ms.map fun m => (specCps m.key, SV.json m.val), post) := by
  rw [object, seqLeft_apply, seqLeft_apply, seqRight_apply, byte_cons_self]
  simp only [Option.bind_some]
  cases ms with
  | nil =>
    have hfail : member (F + 1) (we ++ (rbrace :: post)) = none := by
      rw [member, bind_apply,
        ws_eq hwe (notWs_cons (show Specs.JSON.isWs rbrace = false by decide) _)]
      simp only [Option.bind_some, bind_apply]
      rw [string_none (fun c t he => by
        rw [List.cons.injEq] at he; rw [← he.1]; decide)]
      rfl
    have hsep : sepBy (member (F + 1)) (ws *> byte comma) (bodyCps [] we ++ (rbrace :: post))
        = some ([], we ++ (rbrace :: post)) := by
      rw [sepBy_apply]
      cases h : (bodyCps [] we ++ (rbrace :: post)).length with
      | zero => simp only [sepByUpTo_zero]; rfl
      | succ n =>
        rw [sepByUpTo_succ]
        simp only [show bodyCps [] we = we from rfl] at hfail ⊢
        rw [hfail]
    rw [hsep]
    simp only [Option.bind_some, Option.map_eq_some_iff]
    rw [ws_eq hwe (notWs_cons (show Specs.JSON.isWs rbrace = false by decide) _)]
    simp only [Option.bind_some, byte_cons_self, Option.map_some, List.map_nil]
  | cons m ms =>
    have hmwf := hms m (List.mem_cons_self ..)
    have hbody : bodyCps (m :: ms) we ++ (rbrace :: post)
        = SMem.cpsNoWs3 m ++ (m.ws3 ++ ((ms.map fun m' => comma :: SMem.cps m').flatten
            ++ (rbrace :: post))) := by
      simp [bodyCps, SMem.cps, List.append_assoc]
    have hm1 : member (F + 1) (SMem.cpsNoWs3 m ++ (m.ws3 ++
        ((ms.map fun m' => comma :: SMem.cps m').flatten ++ (rbrace :: post))))
        = some ((specCps m.key, SV.json m.val),
            m.ws3 ++ ((ms.map fun m' => comma :: SMem.cps m').flatten ++ (rbrace :: post))) :=
      member_eq hmwf F (notNum_of_ws hmwf.2.2.2.1 (notNum_flatten_rbrace ms post))
    have hlow : ms.length + 1 ≤ (bodyCps (m :: ms) we ++ (rbrace :: post)).length := by
      rw [hbody]
      have h1 := length_flatten_members ms
      have h2 : 1 ≤ (SMem.cpsNoWs3 m).length := by
        cases hx : SMem.cpsNoWs3 m with
        | nil => exact absurd hx (cpsNoWs3_ne_nil m)
        | cons a t => simp
      simp only [List.length_append, List.length_cons]
      omega
    obtain ⟨n, hn⟩ : ∃ n, (bodyCps (m :: ms) we ++ (rbrace :: post)).length = n + 1 := by
      exact ⟨(bodyCps (m :: ms) we ++ (rbrace :: post)).length - 1, by omega⟩
    obtain ⟨wsLast, hwsLast, hrec⟩ := many_members n ms (by omega)
      (fun x hx => hms x (List.mem_cons_of_mem _ hx)) F m.ws3 hmwf.2.2.2.1 post
    have hsep : sepBy (member (F + 1)) (ws *> byte comma)
        (bodyCps (m :: ms) we ++ (rbrace :: post))
        = some ((specCps m.key, SV.json m.val) ::
            (ms.map fun m' => (specCps m'.key, SV.json m'.val)), wsLast ++ (rbrace :: post)) := by
      rw [sepBy_apply, hn, sepByUpTo_succ, hbody, hm1]
      simp only []
      rw [hrec]
      simp
    rw [hsep]
    simp only [Option.bind_some]
    rw [ws_eq hwsLast (notWs_cons (show Specs.JSON.isWs rbrace = false by decide) _)]
    simp only [Option.bind_some, byte_cons_self, Option.map_some, List.map_cons]

/-! ## The whole document -/

theorem length_bodyCps (ms : List SMem) (we : List ℕ) : ms.length ≤ (bodyCps ms we).length := by
  cases ms with
  | nil => simp
  | cons m ms =>
    have h1 := length_flatten_members ms
    have h2 : 1 ≤ (SMem.cpsNoWs3 m).length := by
      cases hx : SMem.cpsNoWs3 m with
      | nil => exact absurd hx (cpsNoWs3_ne_nil m)
      | cons a t => simp
    have h3 : 1 ≤ (SMem.cps m).length := by rw [SMem.cps, List.length_append]; omega
    simp only [bodyCps, List.length_append, List.length_cons]
    omega

theorem length_serCps (sr : Ser) : sr.body.length + 2 ≤ (Ser.cps sr).length := by
  have := length_bodyCps sr.body sr.wsEmpty
  simp only [Ser.cps, List.length_append, List.length_cons, List.length_nil]
  omega

set_option maxHeartbeats 1000000 in
theorem document_eq {sr : Ser} (h : sr.SWF) : document (Ser.cps sr) = some (sr.json, []) := by
  obtain ⟨hpre, hwe, hpost, hms⟩ := h
  have hlen := length_serCps sr
  obtain ⟨F, hF⟩ : ∃ F, (Ser.cps sr).length = F + 1 :=
    ⟨(Ser.cps sr).length - 1, by omega⟩
  have hFge : sr.body.length ≤ F := by omega
  have hcps : Ser.cps sr
      = sr.pre ++ (lbrace :: (bodyCps sr.body sr.wsEmpty ++ (rbrace :: sr.post))) := by
    simp [Ser.cps, List.append_assoc]
  have hobj : object (F + 1) (lbrace :: (bodyCps sr.body sr.wsEmpty ++ (rbrace :: sr.post)))
      = some (sr.body.map fun m => (specCps m.key, SV.json m.val), sr.post) :=
    object_eq hms hwe F hFge
  rw [document, hF]
  rw [seqLeft_apply, seqLeft_apply]
  have hval : value (F + 1 + 1) (Ser.cps sr) = some (sr.json, sr.post) := by
    rw [hcps, value, seqRight_apply,
      ws_eq hpre (notWs_cons (show Specs.JSON.isWs lbrace = false by decide) _)]
    simp only [Option.bind_some]
    rw [alt_apply, orElse_apply_of_some (show (JSON.obj <$> object (F + 1))
        (lbrace :: (bodyCps sr.body sr.wsEmpty ++ (rbrace :: sr.post)))
        = some (sr.json, sr.post) by rw [map_apply, hobj]; rfl)]
  rw [hval]
  simp only [Option.bind_some]
  rw [show sr.post = sr.post ++ [] from by simp, ws_eq hpost notWs_nil]
  simp

/-- **A serialization parses to its JSON value.** -/
theorem parseBytes_eq {sr : Ser} (h : sr.SWF) :
    Specs.JSON.parseBytes sr.bytes = some sr.json := by
  rw [Specs.JSON.parseBytes, Utf8.utf8_decode (utf8_ser h)]
  simp only [Option.bind_some, document_eq h, Option.map_some]

end SerParse

end Solution.JSONExtract
