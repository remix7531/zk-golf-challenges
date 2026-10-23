import Solution.JSONExtract.GrammarInv

/-!
# A Google ID token is a serialization (`JSONExtract`)

The last step of the backward direction: a byte string that `parseBytes`
accepts as a token of the Google schema *is* `Ser.bytes` of a well-formed
`Serial.Ser`.  `GrammarInv.lean` inverts the grammar into the structure of a
flat object; here the schema conditions of `IsToken` supply the claim-dependent
half of `Ser.WF` (value shapes, the member cap, one member per known key), and
the byte equality comes from the canonicality of UTF-8 (`ParseInv.utf8_bytes`
applied to `SerParse.utf8_ser`).
-/

namespace Solution.JSONExtract

namespace ParseInv

open Specs
open Specs.JSON
open Specs.JSONSchema
open Specs.JSONExtract
open Specs.Parser
open Serial
open SerParse
open SerToken
open Model (Claim nClaims claimName claimCap isStrClaim isIntClaim)

/-! ## Scalars and the schema table -/

theorem holds_isScalar {vs : ValueSpec} {x : JSON} (h : vs.Holds x) : IsScalar x := by
  cases vs <;> cases x <;> first | exact trivial | exact h.elim

theorem gfield_mem : ∀ k : Claim, gfield k ∈ google.fields := by decide

/-! ## The value of a member is admissible for its claim -/

theorem sv_json_str {v : SV} {s : List ℕ} (h : SV.json v = .str s) :
    ∃ body, v = .str body ∧ specCps body = s := by
  cases v with
  | str body => exact ⟨body, rfl, by injection h⟩
  | num n => exact absurd h (by simp [SV.json])
  | btrue => exact absurd h (by simp [SV.json])
  | bfalse => exact absurd h (by simp [SV.json])
  | null => exact absurd h (by simp [SV.json])

theorem sv_ok_of_memberOk {m : SMem} (hkey : ∀ e ∈ m.key, e.WF) (hwf : m.val.WF)
    (hok : google.MemberOk (m.skey, SV.json m.val)) : SV.Ok m.claim m.val := by
  cases hc : m.claim with
  | none => exact trivial
  | some k =>
    have hskey : m.skey = claimName k := (claim_iff_skey hkey k).mp hc
    rw [Schema.MemberOk, show (m.skey, SV.json m.val).1 = m.skey from rfl, hskey,
      field?_claimName] at hok
    have hok2 : ValueSpec.Holds (gfield k).spec (SV.json m.val) := hok
    clear hok
    show (if isStrClaim k = true then
        ∃ body, m.val = .str body ∧ (∀ e ∈ body, e.mcp < 0x80) ∧ body.length ≤ claimCap k
      else if isIntClaim k = true then
        ∃ n, m.val = .num n ∧ n.frac = [] ∧ n.exp = none ∧ n.ints.length ≤ claimCap k
      else m.val = .btrue ∨ m.val = .bfalse)
    by_cases hs : isStrClaim k = true
    · rw [if_pos hs]
      rw [gfield_str hs] at hok2
      cases hmv : m.val with
      | str body =>
        rw [hmv] at hok2 hwf
        have hok' : IsAscii (specCps body) ∧ (specCps body).length ≤ claimCap k := hok2
        have hbwf : ∀ e ∈ body, e.WF := hwf
        have heq : specCps body = mcps body := specCps_eq_mcps' body hbwf hok'.1
        refine ⟨body, rfl, ?_, ?_⟩
        · intro e he
          refine hok'.1 e.mcp ?_
          rw [heq]
          simp only [mcps, List.mem_map]
          exact ⟨e, he, rfl⟩
        · have := hok'.2
          rw [heq] at this
          simpa only [mcps, List.length_map] using this
      | num n => rw [hmv] at hok2; exact hok2.elim
      | btrue => rw [hmv] at hok2; exact hok2.elim
      | bfalse => rw [hmv] at hok2; exact hok2.elim
      | null => rw [hmv] at hok2; exact hok2.elim
    · rw [if_neg hs]
      simp only [Bool.not_eq_true] at hs
      by_cases hi : isIntClaim k = true
      · rw [if_pos hi]
        rw [gfield_int hi] at hok2
        cases hmv : m.val with
        | num n =>
          rw [hmv] at hok2 hwf
          have hok' : (jnumOf n).fracDigits = [] ∧ (jnumOf n).expDigits = [] ∧
            (jnumOf n).intDigits.length ≤ claimCap k := hok2
          have hnwf : n.WF := hwf
          refine ⟨n, rfl, hok'.1, ?_, hok'.2.2⟩
          cases hex : n.exp with
          | none => rfl
          | some e =>
            exfalso
            have hne : e.digits ≠ [] := by
              have := hnwf.2.2
              rw [hex] at this
              exact this.2.2.1
            have : (jnumOf n).expDigits = e.digits := by
              simp only [jnumOf, hex, Option.map_some, Option.getD_some]
            rw [this] at hok'
            exact hne hok'.2.1
        | str body => rw [hmv] at hok2; exact hok2.elim
        | btrue => rw [hmv] at hok2; exact hok2.elim
        | bfalse => rw [hmv] at hok2; exact hok2.elim
        | null => rw [hmv] at hok2; exact hok2.elim
      · rw [if_neg hi]
        simp only [Bool.not_eq_true] at hi
        rw [gfield_bool hs hi] at hok2
        cases hmv : m.val with
        | btrue => exact Or.inl rfl
        | bfalse => exact Or.inr rfl
        | str body => rw [hmv] at hok2; exact hok2.elim
        | num n => rw [hmv] at hok2; exact hok2.elim
        | null => rw [hmv] at hok2; exact hok2.elim

/-! ## The inversion -/

set_option maxHeartbeats 1000000 in
theorem parse_inv {bs : List ℕ} {j : JSON} (hparse : parseBytes bs = some j)
    (htoken : IsToken google j) : ∃ sr : Ser, sr.WF ∧ bs = sr.bytes ∧ sr.json = j := by
  cases j with
  | null => exact htoken.elim
  | bool b => exact htoken.elim
  | num n => exact htoken.elim
  | str s => exact htoken.elim
  | arr es => exact htoken.elim
  | obj ms =>
    obtain ⟨hlen, huniq, hmem⟩ := htoken
    rw [parseBytes] at hparse
    cases hd : utf8Decode bs with
    | none => rw [hd] at hparse; simp at hparse
    | some cps =>
      rw [hd] at hparse
      simp only [Option.bind_some] at hparse
      cases hdoc : document cps with
      | none => rw [hdoc] at hparse; simp at hparse
      | some pr =>
        obtain ⟨jj, rem⟩ := pr
        rw [hdoc] at hparse
        simp only [Option.map_some, Option.some.injEq] at hparse
        subst hparse
        obtain ⟨hbs, hvalid⟩ := utf8Decode_inv hd
        have hsc : ∀ a ∈ ms, IsScalar a.2 := by
          intro a ha
          have hok := hmem a ha
          rw [Schema.MemberOk] at hok
          cases hf : google.field? a.1 with
          | none => rw [hf] at hok; exact hok
          | some fd => rw [hf] at hok; exact holds_isScalar hok
        obtain ⟨sr, hstruct, hmap, hcps⟩ := document_inv hvalid hdoc hsc
        have hbody : ∀ m ∈ sr.body, m.WF := by
          intro m hm
          obtain ⟨h0, h1, h2, h3, hkey, hvwf⟩ := hstruct.2.2.2 m hm
          refine ⟨h0, h1, h2, h3, hkey, hvwf, ?_⟩
          refine sv_ok_of_memberOk hkey hvwf (hmem _ ?_)
          rw [← hmap]
          exact List.mem_map.mpr ⟨m, hm, rfl⟩
        have hswf : sr.SWF := ⟨hstruct.1, hstruct.2.1, hstruct.2.2.1, hbody⟩
        have hlen' : sr.body.length ≤ maxMembers := by
          have hl : sr.body.length = ms.length := by rw [← hmap]; simp
          rw [hl]
          exact hlen
        have huniq' : ∀ k : Claim,
            (sr.body.filter fun m => decide (m.claim = some k)).length ≤ 1 := by
          intro k
          have hf := huniq (gfield k) (gfield_mem k)
          rw [← hmap] at hf
          rw [filter_map_len] at hf
          calc (sr.body.filter fun m => decide (m.claim = some k)).length
              = (sr.body.filter fun m =>
                  decide ((m.skey, SV.json m.val).1 = (gfield k).name)).length := by
                refine congrArg List.length (List.filter_congr fun m hm => ?_)
                simp only [gfield_name, decide_eq_decide]
                exact claim_iff_skey (hbody m hm).2.2.2.2.1 k
            _ ≤ 1 := hf
        have hwf : sr.WF := ⟨hswf.1, hswf.2.1, hswf.2.2.1, hbody, hlen', huniq'⟩
        refine ⟨sr, hwf, ?_, ?_⟩
        · rw [hbs, hcps]
          exact (utf8_bytes (utf8_ser hswf)).symm
        · show JSON.obj (sr.body.map fun m => (m.skey, SV.json m.val)) = JSON.obj ms
          rw [hmap]

end ParseInv

end Solution.JSONExtract
