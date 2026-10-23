import Solution.JSONExtract.RunInv
import Solution.JSONExtract.TokenInv

/-!
# The two model-level bridges (`JSONExtract`)

`Main.soundness` and `Main.completeness` reduce, through the loop invariant over
the 1024 `Step`s, to two statements that mention no circuit at all: they relate
the automaton of `Model.lean` to the trusted JSON specification.

* `sound_bridge`: an accepting run over `bytes[0 .. len)` means the prefix parses
  as a JSON document, that document is a token of the Google schema, and the
  run's slot read-outs are exactly the encoding of its claims.
* `complete_bridge`: conversely, a token makes the honest run accept.

`sound_bridge` is proved here from the serialization machinery: `RunInv.ser_inv`
turns an accepting run into a `Ser`, `SerParse.parseBytes_eq` parses it,
`SerToken.isToken`/`SerToken.encode_eq` give the schema and the claims, and
`SerRun.ser_accepts` matches the run's read-outs with the members' slots.

`complete_bridge` is the converse of `SerParse`: `ParseInv.parse_inv`
(`ParseInv.lean`, `GrammarInv.lean`, `TokenInv.lean`) inverts the trusted parser
and turns a token of the schema into a well-formed `Ser`, and
`SerRun.ser_accepts` then makes the honest run accept it.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nClaims Claim)

namespace ModelBridge

open Model

/-! ## The slots the run reads out -/

/-- Claim `k`'s string slot, read off the run. -/
def expectedStr (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) (n : ℕ) :
    Specs.JSONExtract.StrSlot n where
  present := presentCount bytes len k
  len := slotLen bytes len k
  bytes := Vector.ofFn fun t : Fin n => cell bytes len k t.val

/-- Claim `k`'s integer slot, read off the run. -/
def expectedInt (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) (n : ℕ) :
    Specs.JSONExtract.IntSlot n where
  present := presentCount bytes len k
  negative := signCount bytes len k
  len := slotLen bytes len k
  digits := Vector.ofFn fun t : Fin n => cell bytes len k t.val

/-- Claim `k`'s boolean slot, read off the run. -/
def expectedBool (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) : Specs.JSONExtract.BoolSlot where
  present := presentCount bytes len k
  value := trueCount bytes len k

/-- The whole output, read off the run. -/
def expected (bytes : ℕ → ℕ) (len : ℕ) : Specs.JSONExtract.ExpectedOutput where
  iss := expectedStr bytes len 0 _
  sub := expectedStr bytes len 1 _
  aud := expectedStr bytes len 2 _
  azp := expectedStr bytes len 3 _
  hd := expectedStr bytes len 4 _
  email := expectedStr bytes len 5 _
  emailVerified := expectedBool bytes len 6
  nonce := expectedStr bytes len 7 _
  atHash := expectedStr bytes len 8 _
  iat := expectedInt bytes len 9 _
  exp := expectedInt bytes len 10 _

/-! ## Acceptance, unpacked -/

theorem accepts_iff (bytes : ℕ → ℕ) (len : ℕ) :
    accepts bytes len = true ↔
      ((∀ i, i < len → (step (run bytes len i) (bytes i)).isSome) ∧
        (run bytes len len).st = St.END ∧ (run bytes len len).sub = Sub.PLAIN ∧
        (run bytes len len).nMem ≤ maxMembers ∧
        ∀ k : Claim, presentCount bytes len k ≤ 1) := by
  simp only [accepts, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun k => h5 k (List.mem_finRange k)⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun k _ => h5 k⟩

/-! ## The bridges -/

set_option maxHeartbeats 1000000 in
/-- **Soundness bridge.**  An accepting run of the model on `bytes[0 .. len)`
means the prefix is a Google ID token, and the model's slot read-outs are the
encoding of its claims. -/
theorem sound_bridge (bytes : ℕ → ℕ) (len : ℕ) (hlen : len ≤ bufferLen)
    (hbytes : ∀ i, i < len → bytes i < 256) (hacc : accepts bytes len = true) :
    ∃ j, Specs.JSON.parseBytes (List.ofFn fun i : Fin len => bytes i) = some j ∧
      Specs.JSONSchema.IsToken Specs.JSONExtract.google j ∧
      Specs.JSONExtract.encodeOutput (Specs.JSONExtract.GoogleClaims.ofJSON j)
        = expected bytes len := by
  obtain ⟨hsteps, hendst, hsubP, hmem, hpres⟩ := (accepts_iff bytes len).mp hacc
  obtain ⟨hrun, htrace⟩ := RunList.run_toL hsteps len le_rfl
  obtain ⟨sr, hswf, hL⟩ := RunInv.ser_inv (RunList.toL bytes len) hrun hendst
  obtain ⟨r', hrun', hend', hsub', hnmem', hcon⟩ := SerRun.ser_run hswf
  rw [← hL] at hrun' hcon
  have hr' : r' = run bytes len len := Option.some.inj (hrun'.symm.trans hrun)
  have hwf : sr.WF := by
    refine ⟨hswf.1, hswf.2.1, hswf.2.2.1, hswf.2.2.2, ?_, ?_⟩
    · rw [← hnmem', hr']; exact hmem
    · intro k
      rw [← SerRun.bMatch_eq_filter, ← hcon.1 k]
      have := RunList.presentCount_eq hsteps k
      rw [SerStep.cMatch, ← this]
      exact hpres k
  obtain ⟨-, hpresE, hslot, hsign, htrue, hcell⟩ := SerRun.ser_accepts hwf hL
  refine ⟨sr.json, ?_, SerToken.isToken hwf, ?_⟩
  · rw [← RunList.toL_eq_ofFn, hL]
    exact SerParse.parseBytes_eq hswf
  · rw [SerToken.encode_eq hwf]
    have hstr : ∀ (k : Claim) (nn : ℕ),
        (Model.isStrClaim k = true ∨ Model.isIntClaim k = true) →
        expectedStr bytes len k nn = Serial.strSlotOf sr.body k nn := by
      intro k nn hkind
      simp only [expectedStr, Serial.strSlotOf, hpresE k, hslot k,
        Specs.JSONExtract.StrSlot.mk.injEq, true_and]
      exact Vector.ext fun t ht => by simp [hcell k hkind]
    have hint : ∀ (k : Claim) (nn : ℕ),
        (Model.isStrClaim k = true ∨ Model.isIntClaim k = true) →
        expectedInt bytes len k nn = Serial.intSlotOf sr.body k nn := by
      intro k nn hkind
      simp only [expectedInt, Serial.intSlotOf, hpresE k, hslot k, hsign k,
        Specs.JSONExtract.IntSlot.mk.injEq, true_and]
      exact Vector.ext fun t ht => by simp [hcell k hkind]
    have hbool : ∀ k : Claim, expectedBool bytes len k = Serial.boolSlotOf sr.body k := by
      intro k
      simp only [expectedBool, Serial.boolSlotOf, hpresE k, htrue k]
    simp only [expected, Serial.outputOf, Specs.JSONExtract.ExpectedOutput.mk.injEq]
    exact ⟨(hstr 0 _ (by decide)).symm, (hstr 1 _ (by decide)).symm,
      (hstr 2 _ (by decide)).symm, (hstr 3 _ (by decide)).symm, (hstr 4 _ (by decide)).symm,
      (hstr 5 _ (by decide)).symm, (hbool 6).symm, (hstr 7 _ (by decide)).symm,
      (hstr 8 _ (by decide)).symm, (hint 9 _ (by decide)).symm, (hint 10 _ (by decide)).symm⟩

/-- **Completeness bridge.**  A Google ID token makes the honest run accept. -/
theorem complete_bridge (bytes : ℕ → ℕ) (len : ℕ) (hlen : len ≤ bufferLen)
    (hbytes : ∀ i, i < len → bytes i < 256) (hpad : ∀ i, len ≤ i → bytes i = 0)
    (j : Specs.JSON.JSON)
    (hparse : Specs.JSON.parseBytes (List.ofFn fun i : Fin len => bytes i) = some j)
    (htoken : Specs.JSONSchema.IsToken Specs.JSONExtract.google j) :
    accepts bytes len = true := by
  obtain ⟨sr, hwf, hbs, -⟩ := ParseInv.parse_inv hparse htoken
  exact (SerRun.ser_accepts hwf (by rw [RunList.toL_eq_ofFn]; exact hbs)).1

end ModelBridge
end Solution.JSONExtract
