import Solution.JSONExtract.SerParse

/-!
# A serialization is a Google ID token (`JSONExtract`)

The schema half of the specification argument: the JSON value of a well-formed
`Ser` satisfies `Specs.JSONSchema.IsToken Specs.JSONExtract.google`, and its
claims read back as the slots the model's run reads out.
-/

namespace Solution.JSONExtract

namespace SerToken

open Specs
open Specs.JSON
open Specs.JSONSchema
open Specs.JSONExtract
open Specs.Parser
open Serial
open SerParse
open Model (Claim nClaims claimName claimCap isStrClaim isIntClaim isBoolClaim)

/-! ## The model's and the specification's code points of a key agree on ASCII -/

theorem mcp_cases {e : SE} (h : e.mcp < 0x80) :
    (∃ b, e = .plain b) ∨ (∃ b, e = .esc b) ∨ (∃ a b c d, e = .hex a b c d) := by
  cases e with
  | plain b => exact Or.inl ⟨b, rfl⟩
  | esc b => exact Or.inr (Or.inl ⟨b, rfl⟩)
  | hex a b c d => exact Or.inr (Or.inr ⟨a, b, c, d, rfl⟩)
  | u2 _ _ => exact absurd h (by simp [SE.mcp, Model.nonAsciiMarker])
  | u3 _ _ _ => exact absurd h (by simp [SE.mcp, Model.nonAsciiMarker])
  | u4 _ _ _ _ => exact absurd h (by simp [SE.mcp, Model.nonAsciiMarker])

theorem scp_eq_mcp {e : SE} (h : e.mcp < 0x80) : e.scp = e.mcp := by
  rcases mcp_cases h with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨a, b, c, d, rfl⟩ <;> rfl

theorem isHigh_false {e : SE} (h : e.mcp < 0x80) : e.isHigh = false := by
  rcases mcp_cases h with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨a, b, c, d, rfl⟩
  · rfl
  · rfl
  · simp only [SE.mcp] at h
    simp only [SE.isHigh, isHighSurrogate, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
    left; omega

theorem mcps_cons (e : SE) (l : List SE) : mcps (e :: l) = e.mcp :: mcps l := rfl

theorem specCps_eq_mcps : ∀ (l : List SE), (∀ e ∈ l, e.mcp < 0x80) → specCps l = mcps l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro h
    have he := h e (List.mem_cons_self ..)
    cases l with
    | nil => rw [specCps_single, mcps, List.map_cons, List.map_nil, scp_eq_mcp he]
    | cons e' l' =>
      rw [specCps_cons2, if_neg (by simp [isHigh_false he]), scp_eq_mcp he,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      rfl

theorem mcp_eq_scp {e : SE} (hwf : e.WF) (h : e.scp < 0x80) : e.mcp = e.scp := by
  cases e with
  | plain b => rfl
  | esc b => rfl
  | hex a b c d => rfl
  | u2 b0 b1 =>
    exfalso
    have h' : Model.isLead2 b0 = true ∧ Model.isCont b1 = true := hwf
    have hge := u2_scp_ge h'
    have h2 : (b0 - 0xC0) * 0x40 + (b1 - 0x80) < 0x80 := h
    omega
  | u3 b0 b1 b2 =>
    have h' : ((b0 = 0xE0 ∧ Model.isContA0BF b1 = true) ∨
        (Model.isLead3 b0 = true ∧ Model.isCont b1 = true) ∨
        (b0 = 0xED ∧ Model.isCont809F b1 = true)) ∧ Model.isCont b2 = true := hwf
    exact absurd (show (b0 - 0xE0) * 0x1000 + (b1 - 0x80) * 0x40 + (b2 - 0x80) < 0x80 from h)
      (by have := u3_scp_ge (b2 := b2) h'.1; omega)
  | u4 b0 b1 b2 b3 =>
    have h' : ((b0 = 0xF0 ∧ Model.isCont90BF b1 = true) ∨
        (Model.isLead4 b0 = true ∧ Model.isCont b1 = true) ∨
        (b0 = 0xF4 ∧ Model.isCont808F b1 = true)) ∧ Model.isCont b2 = true ∧
        Model.isCont b3 = true := hwf
    exact absurd (show (b0 - 0xF0) * 0x40000 + (b1 - 0x80) * 0x1000 + (b2 - 0x80) * 0x40
        + (b3 - 0x80) < 0x80 from h)
      (by have := u4_scp_ge (b2 := b2) (b3 := b3) h'.1; omega)

theorem specCps_eq_mcps' : ∀ (l : List SE), (∀ e ∈ l, e.WF) →
    (∀ c ∈ specCps l, c < 0x80) → specCps l = mcps l := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons e l ih =>
    intro hwf h
    cases l with
    | nil =>
      have he : e.scp < 0x80 := h e.scp (by rw [specCps_single]; exact List.mem_cons_self ..)
      rw [specCps_single, mcps, List.map_cons, List.map_nil,
        mcp_eq_scp (hwf e (List.mem_cons_self ..)) he]
    | cons e' l' =>
      by_cases hp : e.isHigh && e'.isLow
      · exfalso
        rw [specCps_cons2, if_pos hp] at h
        have := h _ (List.mem_cons_self ..)
        omega
      · rw [specCps_cons2, if_neg (by simpa using hp)] at h ⊢
        have he : e.scp < 0x80 := h _ (List.mem_cons_self ..)
        rw [mcps_cons, ← mcp_eq_scp (hwf e (List.mem_cons_self ..)) he,
          ih (fun x hx => hwf x (List.mem_cons_of_mem _ hx))
            (fun c hc => h c (List.mem_cons_of_mem _ hc))]

theorem claimName_ascii : ∀ (k : Claim), ∀ c ∈ claimName k, c < 0x80 := by decide

theorem skey_iff_mkey {m : SMem} (hwf : ∀ e ∈ m.key, e.WF) (k : Claim) :
    m.skey = claimName k ↔ m.mkey = claimName k := by
  constructor
  · intro h
    have hasc : ∀ c ∈ specCps m.key, c < 0x80 := by
      rw [show specCps m.key = m.skey from rfl, h]; exact claimName_ascii k
    rw [show m.mkey = mcps m.key from rfl, ← specCps_eq_mcps' m.key hwf hasc]
    exact h
  · intro h
    have hasc : ∀ e ∈ m.key, e.mcp < 0x80 := by
      intro e he
      have : e.mcp ∈ mcps m.key := by
        simp only [mcps, List.mem_map]; exact ⟨e, he, rfl⟩
      rw [show mcps m.key = m.mkey from rfl, h] at this
      exact claimName_ascii k _ this
    rw [show m.skey = specCps m.key from rfl, specCps_eq_mcps m.key hasc]
    exact h

/-! ## The schema table -/

def gfield (k : Claim) : Field := google.fields.getD k.val ⟨[], .bool⟩

theorem field?_claimName (k : Claim) : google.field? (claimName k) = some (gfield k) := by
  revert k; decide

theorem gfield_name (k : Claim) : (gfield k).name = claimName k := by revert k; decide

theorem gfield_str {k : Claim} (h : isStrClaim k = true) :
    (gfield k).spec = ValueSpec.str (claimCap k) := by revert h; revert k; decide

theorem gfield_int {k : Claim} (h : isIntClaim k = true) :
    (gfield k).spec = ValueSpec.int (claimCap k) := by revert h; revert k; decide

theorem gfield_bool {k : Claim} (h1 : isStrClaim k = false) (h2 : isIntClaim k = false) :
    (gfield k).spec = ValueSpec.bool := by revert h1 h2; revert k; decide

theorem fields_named : ∀ f ∈ google.fields, ∃ k : Claim, f.name = claimName k := by decide

theorem field?_none {name : List ℕ} (h : ∀ k : Claim, ¬ (name = claimName k)) :
    google.field? name = none := by
  cases hf : google.field? name with
  | none => rfl
  | some f =>
    exfalso
    rw [Schema.field?] at hf
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    obtain ⟨k, hk⟩ := fields_named f h2
    simp only [decide_eq_true_eq] at h1
    exact h (k) (by rw [← h1, hk])

theorem claim_iff' {m : SMem} (k : Claim) : m.claim = some k ↔ m.mkey = claimName k := by
  constructor
  · intro hh
    have := List.find?_some (p := fun k' : Claim => decide (m.mkey = claimName k')) hh
    simpa using this
  · intro hh
    cases hx : (List.finRange nClaims).find? (fun k' : Claim => decide (m.mkey = claimName k'))
      with
    | none =>
      exact absurd (List.find?_eq_none.mp hx k (List.mem_finRange k)) (by simp [hh])
    | some k' =>
      have hk' := List.find?_some hx
      simp only [decide_eq_true_eq] at hk'
      have hdist : ∀ a b : Claim, claimName a = claimName b → a = b := by decide
      rw [SMem.claim, hx, hdist k k' (by rw [← hh, ← hk'])]

theorem claim_iff_skey {m : SMem} (hwf : ∀ e ∈ m.key, e.WF) (k : Claim) :
    m.claim = some k ↔ m.skey = claimName k :=
  (claim_iff' k).trans (skey_iff_mkey hwf k).symm

theorem filter_map_len {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    ((l.map f).filter p).length = (l.filter fun a => p (f a)).length := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p (f a) <;> simp [h, ih]

/-! ## Scalars -/

theorem isScalar_json (v : SV) : IsScalar (SV.json v) := by
  cases v <;> exact trivial

/-! ## The token -/

set_option maxHeartbeats 1000000 in
theorem isToken {sr : Ser} (h : sr.WF) : IsToken google sr.json := by
  obtain ⟨-, -, -, hms, hlen, huniq⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Ser.json, List.length_map]
    exact hlen
  · intro f hf
    obtain ⟨k, hk⟩ := fields_named f hf
    have hmwf : ∀ m ∈ sr.body, ∀ e ∈ m.key, e.WF := fun m hm => (hms m hm).2.2.2.2.1
    calc ((sr.body.map fun m => (m.skey, SV.json m.val)).filter
            fun p => decide (p.1 = f.name)).length
        = (sr.body.filter fun m => decide (m.skey = f.name)).length := filter_map_len _ _ _
      _ = (sr.body.filter fun m => decide (m.claim = some k)).length := by
          refine congrArg List.length (List.filter_congr fun m hm => ?_)
          rw [hk]
          simp only [decide_eq_decide]
          exact (claim_iff_skey (hmwf m hm) k).symm
      _ ≤ 1 := huniq k
  · intro p hp
    simp only [Ser.json, List.mem_map] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    obtain ⟨-, -, -, -, hkey, hvwf, hvok⟩ := hms m hm
    rw [Schema.MemberOk]
    by_cases hc : ∃ k : Claim, m.claim = some k
    · obtain ⟨k, hk⟩ := hc
      have hskey : m.skey = claimName k := (claim_iff_skey hkey k).mp hk
      rw [show (m.skey, SV.json m.val).1 = m.skey from rfl, hskey, field?_claimName]
      show ValueSpec.Holds (gfield k).spec (SV.json m.val)
      have hok : (if isStrClaim k = true then
            ∃ body, m.val = .str body ∧ (∀ e ∈ body, e.mcp < 0x80) ∧ body.length ≤ claimCap k
          else if isIntClaim k = true then
            ∃ n, m.val = .num n ∧ n.frac = [] ∧ n.exp = none ∧ n.ints.length ≤ claimCap k
          else m.val = .btrue ∨ m.val = .bfalse) := by
        have : SV.Ok (some k) m.val := by rw [← hk]; exact hvok
        exact this
      by_cases hs : isStrClaim k = true
      · rw [if_pos hs] at hok
        obtain ⟨body, hbody, hascii, hblen⟩ := hok
        rw [gfield_str hs, hbody]
        refine ⟨?_, ?_⟩
        · intro c hc'
          rw [specCps_eq_mcps body hascii] at hc'
          simp only [mcps, List.mem_map] at hc'
          obtain ⟨e, he, rfl⟩ := hc'
          exact hascii e he
        · rw [specCps_eq_mcps body hascii]
          simpa [mcps] using hblen
      · rw [if_neg hs] at hok
        simp only [Bool.not_eq_true] at hs
        by_cases hi : isIntClaim k = true
        · rw [if_pos hi] at hok
          obtain ⟨nm, hnm, hfr, hex, hilen⟩ := hok
          rw [gfield_int hi, hnm]
          exact ⟨hfr, by simp [hex], hilen⟩
        · rw [if_neg hi] at hok
          simp only [Bool.not_eq_true] at hi
          rw [gfield_bool hs hi]
          rcases hok with hb | hb <;> rw [hb] <;> exact trivial
    · push_neg at hc
      have hnone : ∀ k : Claim, ¬ (m.skey = claimName k) := by
        intro k hkk
        exact hc k ((claim_iff_skey hkey k).mpr hkk)
      rw [show (m.skey, SV.json m.val).1 = m.skey from rfl, field?_none hnone]
      show IsScalar (SV.json m.val)
      exact isScalar_json m.val

/-! ## At most one member per claim -/

theorem sum_of_le_one {α : Type} (p : α → Bool) (g : α → ℕ) : ∀ (l : List α),
    (l.filter p).length ≤ 1 →
    (l.map fun x => if p x = true then g x else 0).sum = (l.find? p).elim 0 g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro hl
    rw [List.filter_cons] at hl
    by_cases ha : p a = true
    · rw [if_pos (show p a = true from ha), List.length_cons] at hl
      have hnil : l.filter p = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hall : ∀ x ∈ l, p x = false := by
        intro x hx
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        have : x ∈ l.filter p := List.mem_filter.mpr ⟨hx, hc⟩
        rw [hnil] at this; simp at this
      have hz : (l.map fun x => if p x = true then g x else 0).sum = 0 := by
        rw [List.sum_eq_zero]
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [if_neg (by simp [hall x hx])]
      rw [List.map_cons, List.sum_cons, if_pos ha, hz, List.find?_cons_of_pos ha]
      simp
    · simp only [Bool.not_eq_true] at ha
      rw [if_neg (by simp [ha])] at hl
      rw [List.map_cons, List.sum_cons, if_neg (by simp [ha]),
        List.find?_cons_of_neg (by simp [ha]), ih hl]
      simp

theorem flatten_of_le_one {α β : Type} (p : α → Bool) (g : α → List β) : ∀ (l : List α),
    (l.filter p).length ≤ 1 →
    (l.map fun x => if p x = true then g x else []).flatten = (l.find? p).elim [] g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro hl
    rw [List.filter_cons] at hl
    by_cases ha : p a = true
    · rw [if_pos (show p a = true from ha), List.length_cons] at hl
      have hnil : l.filter p = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hall : ∀ x ∈ l, p x = false := by
        intro x hx
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        have : x ∈ l.filter p := List.mem_filter.mpr ⟨hx, hc⟩
        rw [hnil] at this; simp at this
      have hz : (l.map fun x => if p x = true then g x else []).flatten = [] := by
        rw [List.flatten_eq_nil_iff]
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [if_neg (by simp [hall x hx])]
      rw [List.map_cons, List.flatten_cons, if_pos ha, hz, List.find?_cons_of_pos ha]
      simp
    · simp only [Bool.not_eq_true] at ha
      rw [if_neg (by simp [ha])] at hl
      rw [List.map_cons, List.flatten_cons, if_neg (by simp [ha]),
        List.find?_cons_of_neg (by simp [ha]), ih hl]
      simp

theorem slot_facts {sr : Ser} (h : sr.WF) (k : Claim) :
    ((sr.body.find? fun m => decide (m.claim = some k)) = none ∧ bMatch sr.body k = 0 ∧
      bVals sr.body k = [] ∧ bSign sr.body k = 0 ∧ bTrue sr.body k = 0)
    ∨ (∃ m, (sr.body.find? fun m' => decide (m'.claim = some k)) = some m ∧ m ∈ sr.body ∧
        m.claim = some k ∧ bMatch sr.body k = 1 ∧ bVals sr.body k = m.val.vals ∧
        bSign sr.body k = m.val.sign ∧ bTrue sr.body k = m.val.trues) := by
  have huniq := h.2.2.2.2.2 k
  set p : SMem → Bool := fun m => decide (m.claim = some k) with hp
  have e1 : bMatch sr.body k = (sr.body.find? p).elim 0 (fun _ => 1) := by
    rw [bMatch, ← sum_of_le_one p (fun _ => 1) sr.body huniq]
    exact congrArg _ (List.map_congr_left fun m _ => by simp only [hp, decide_eq_true_eq])
  have e2 : bVals sr.body k = (sr.body.find? p).elim [] (fun m => m.val.vals) := by
    rw [bVals, ← flatten_of_le_one p (fun m => m.val.vals) sr.body huniq]
    exact congrArg _ (List.map_congr_left fun m _ => by simp only [hp, decide_eq_true_eq])
  have e3 : bSign sr.body k = (sr.body.find? p).elim 0 (fun m => m.val.sign) := by
    rw [bSign, ← sum_of_le_one p (fun m => m.val.sign) sr.body huniq]
    exact congrArg _ (List.map_congr_left fun m _ => by simp only [hp, decide_eq_true_eq])
  have e4 : bTrue sr.body k = (sr.body.find? p).elim 0 (fun m => m.val.trues) := by
    rw [bTrue, ← sum_of_le_one p (fun m => m.val.trues) sr.body huniq]
    exact congrArg _ (List.map_congr_left fun m _ => by simp only [hp, decide_eq_true_eq])
  cases hf : sr.body.find? p with
  | none => left; rw [hf] at e1 e2 e3 e4; exact ⟨rfl, e1, e2, e3, e4⟩
  | some m =>
    right
    refine ⟨m, rfl, List.mem_of_find?_eq_some hf, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (have := List.find?_some hf; simpa [hp] using this)
        | (rw [hf] at e1 e2 e3 e4; first | exact e1 | exact e2 | exact e3 | exact e4)

/-! ## Reading the claims back -/

theorem find?_map_local {α β : Type} (f : α → β) (p : β → Bool) : ∀ (l : List α),
    (l.map f).find? p = (l.find? fun a => p (f a)).map f := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p (f a) = true
    · rw [List.map_cons, List.find?_cons_of_pos h,
        List.find?_cons_of_pos (p := fun a => p (f a)) h]
      rfl
    · simp only [Bool.not_eq_true] at h
      rw [List.map_cons, List.find?_cons_of_neg (by simp [h]),
        List.find?_cons_of_neg (by simp [h]), ih]

theorem find?_congr_local {α : Type} {p q : α → Bool} : ∀ (l : List α), (∀ a ∈ l, p a = q a) →
    l.find? p = l.find? q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    have ha := h a (List.mem_cons_self ..)
    by_cases hp : p a = true
    · rw [List.find?_cons_of_pos hp, List.find?_cons_of_pos (by rw [← ha]; exact hp)]
    · simp only [Bool.not_eq_true] at hp
      rw [List.find?_cons_of_neg (by simp [hp]),
        List.find?_cons_of_neg (by rw [← ha]; simp [hp]),
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem lookup_eq {sr : Ser} (h : sr.WF) (k : Claim) :
    lookup (members sr.json) (claimName k)
      = (sr.body.find? fun m => decide (m.claim = some k)).map fun m => SV.json m.val := by
  have hmwf : ∀ m ∈ sr.body, ∀ e ∈ m.key, e.WF := fun m hm => (h.2.2.2.1 m hm).2.2.2.2.1
  show ((sr.body.map fun m => (m.skey, SV.json m.val)).find?
      fun p => decide (p.1 = claimName k)).map (fun p => p.2) = _
  rw [find?_map_local, find?_congr_local sr.body (p := fun m => decide (m.skey = claimName k))
    (q := fun m => decide (m.claim = some k)) (fun m hm => by
      simp only [decide_eq_decide]
      exact (claim_iff_skey (hmwf m hm) k).symm)]
  cases sr.body.find? fun m => decide (m.claim = some k) <;> rfl

theorem valOk_cases {sr : Ser} (h : sr.WF) {m : SMem} (hm : m ∈ sr.body) {k : Claim}
    (hck : m.claim = some k) :
    (if isStrClaim k = true then
        ∃ body, m.val = .str body ∧ (∀ e ∈ body, e.mcp < 0x80) ∧ body.length ≤ claimCap k
      else if isIntClaim k = true then
        ∃ nm, m.val = .num nm ∧ nm.frac = [] ∧ nm.exp = none ∧ nm.ints.length ≤ claimCap k
      else m.val = .btrue ∨ m.val = .bfalse) := by
  obtain ⟨-, -, -, -, -, -, hvok⟩ := h.2.2.2.1 m hm
  have : SV.Ok (some k) m.val := by rw [← hck]; exact hvok
  exact this

theorem strSlot_eq {sr : Ser} (h : sr.WF) {k : Claim} (hs : isStrClaim k = true) (n : ℕ) :
    encodeStr (n := n) ((lookup (members sr.json) (claimName k)).bind asString)
      = strSlotOf sr.body k n := by
  rw [lookup_eq h k]
  rcases slot_facts h k with ⟨hf, h1, h2, h3, h4⟩ | ⟨m, hf, hm, hck, h1, h2, h3, h4⟩
  · rw [hf]
    simp [encodeStr, strSlotOf, h1, h2, padTo]
  · have hok := valOk_cases h hm hck
    rw [if_pos hs] at hok
    obtain ⟨body, hbody, hascii, -⟩ := hok
    have h2' : bVals sr.body k = mcps body := by rw [h2, hbody]; rfl
    rw [hf]
    simp only [Option.map_some, Option.bind_some, hbody]
    rw [show SV.json (SV.str body) = JSON.str (specCps body) from rfl,
      specCps_eq_mcps body hascii]
    simp [asString, encodeStr, strSlotOf, h1, h2', padTo]

theorem intSlot_eq {sr : Ser} (h : sr.WF) {k : Claim} (hs : isStrClaim k = false)
    (hi : isIntClaim k = true) (n : ℕ) :
    encodeInt (n := n) ((lookup (members sr.json) (claimName k)).bind asInt)
      = intSlotOf sr.body k n := by
  rw [lookup_eq h k]
  rcases slot_facts h k with ⟨hf, h1, h2, h3, h4⟩ | ⟨m, hf, hm, hck, h1, h2, h3, h4⟩
  · rw [hf]
    simp [encodeInt, intSlotOf, h1, h2, h3, padTo]
  · have hok := valOk_cases h hm hck
    rw [if_neg (by simp [hs]), if_pos hi] at hok
    obtain ⟨nm, hnm, -, -, -⟩ := hok
    have h2' : bVals sr.body k = nm.ints := by rw [h2, hnm]; rfl
    have h3' : bSign sr.body k = (if nm.neg then 1 else 0) := by rw [h3, hnm]; rfl
    rw [hf]
    simp only [Option.map_some, Option.bind_some, hnm]
    rw [show SV.json (SV.num nm) = JSON.num (jnumOf nm) from rfl]
    simp [asInt, encodeInt, intSlotOf, h1, h2', h3', padTo, jnumOf]

theorem boolSlot_eq {sr : Ser} (h : sr.WF) {k : Claim} (hs : isStrClaim k = false)
    (hi : isIntClaim k = false) :
    encodeBool ((lookup (members sr.json) (claimName k)).bind asBool) = boolSlotOf sr.body k := by
  rw [lookup_eq h k]
  rcases slot_facts h k with ⟨hf, h1, h2, h3, h4⟩ | ⟨m, hf, hm, hck, h1, h2, h3, h4⟩
  · rw [hf]
    simp [encodeBool, boolSlotOf, h1, h4]
  · have hok := valOk_cases h hm hck
    rw [if_neg (by simp [hs]), if_neg (by simp [hi])] at hok
    rw [hf]
    rcases hok with hb | hb
    · have h4' : bTrue sr.body k = 1 := by rw [h4, hb]; rfl
      simp only [Option.map_some, Option.bind_some, hb]
      rw [show SV.json SV.btrue = JSON.bool true from rfl]
      simp [asBool, encodeBool, boolSlotOf, h1, h4']
    · have h4' : bTrue sr.body k = 0 := by rw [h4, hb]; rfl
      simp only [Option.map_some, Option.bind_some, hb]
      rw [show SV.json SV.bfalse = JSON.bool false from rfl]
      simp [asBool, encodeBool, boolSlotOf, h1, h4']

theorem key_names : key "iss" = claimName 0 ∧ key "sub" = claimName 1 ∧
    key "aud" = claimName 2 ∧ key "azp" = claimName 3 ∧ key "hd" = claimName 4 ∧
    key "email" = claimName 5 ∧ key "email_verified" = claimName 6 ∧
    key "nonce" = claimName 7 ∧ key "at_hash" = claimName 8 ∧ key "iat" = claimName 9 ∧
    key "exp" = claimName 10 := by decide

set_option maxHeartbeats 1000000 in
/-- **The claims of a serialization are the slots of its members.** -/
theorem encode_eq {sr : Ser} (h : sr.WF) :
    encodeOutput (GoogleClaims.ofJSON sr.json) = outputOf sr.body := by
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := key_names
  simp only [encodeOutput, outputOf, GoogleClaims.ofJSON, n0, n1, n2, n3, n4, n5, n6, n7, n8,
    n9, n10, Specs.JSONExtract.ExpectedOutput.mk.injEq]
  exact ⟨strSlot_eq h (by decide) _, strSlot_eq h (by decide) _, strSlot_eq h (by decide) _,
    strSlot_eq h (by decide) _, strSlot_eq h (by decide) _, strSlot_eq h (by decide) _,
    boolSlot_eq h (by decide) (by decide), strSlot_eq h (by decide) _,
    strSlot_eq h (by decide) _, intSlot_eq h (by decide) (by decide) _,
    intSlot_eq h (by decide) (by decide) _⟩

end SerToken

end Solution.JSONExtract
