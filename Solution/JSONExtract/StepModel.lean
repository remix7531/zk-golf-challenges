import Solution.JSONExtract.StepSpec
import Solution.JSONExtract.AutomatonModel

/-!
# Reading one position's rows against the model (`JSONExtract`)

`StepSpec.lean`'s `RowSpec` is the exact field identity every row of
`Step.main` enforces, written in the value-level twins of `StepTheorems.lean`.
This file turns those identities into the statement `Step.Spec` makes about a
`Model.Regs` the `*Prev` half encodes: one lemma per derived signal, then one
per register, and finally the composition `spec_of_rows`.

Everything here is pure: no circuit, no `ConstraintsHold`.  The vocabulary is
`ByteClass.ind` (the `0/1` indicator of a `Bool`) on the circuit side and
`Model.signals` on the model side.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSt nSub nClaims kIdxMax ofsMax St Sub Claim Regs)
open ByteClass (ind)

namespace Step

open Model.St Model.Sub

variable {inp : Inputs (F circomPrime)} {r : Regs}

/-! ## Pure `ind` arithmetic on the state spaces

Each derived signal is an affine combination of one-hot entries; the `Bool`
side of each identity is decidable, so the state-space case split happens once,
here, and the lemmas about a position only rewrite the one-hot entries. -/

open ByteClass (ind_add_disj ind_sub one_sub_ind ind_mul)

/-- The model's "a value is being read" gate (the `inVal` local of `Model.step`). -/
def inValP (s : St) : Bool :=
  s ≠ St.PRE && s ≠ St.OBJ && s ≠ St.KEY && s ≠ St.AKEY && s ≠ St.PVAL && s ≠ St.AVAL &&
    s ≠ St.SEP && s ≠ St.END

lemma inStr_ind (s : St) :
    ind (decide (s = St.KEY)) + ind (decide (s = St.STR)) = ind (Model.inStr s) := by
  rw [ind_add_disj (by revert s; decide)]
  congr 1

lemma inH_ind (sb : Sub) :
    ind (decide (sb = Sub.H1)) + ind (decide (sb = Sub.H2)) + ind (decide (sb = Sub.H3))
      = ind (decide (sb = Sub.H1) || decide (sb = Sub.H2) || decide (sb = Sub.H3)) := by
  rw [ind_add_disj (by revert sb; decide), ind_add_disj (by revert sb; decide)]

lemma inVal_ind (s : St) :
    (1 : F circomPrime) - ind (decide (s = St.PRE)) - ind (decide (s = St.OBJ))
        - ind (decide (s = St.KEY)) - ind (decide (s = St.AKEY)) - ind (decide (s = St.PVAL))
        - ind (decide (s = St.AVAL)) - ind (decide (s = St.SEP)) - ind (decide (s = St.END))
      = ind (inValP s) := by
  rw [one_sub_ind, ind_sub (by revert s; decide), ind_sub (by revert s; decide),
    ind_sub (by revert s; decide), ind_sub (by revert s; decide), ind_sub (by revert s; decide),
    ind_sub (by revert s; decide), ind_sub (by revert s; decide)]
  congr 1
  revert s; decide

lemma kStr_ind (c : Option Claim) :
    ind (decide (c = some 0)) + ind (decide (c = some 1)) + ind (decide (c = some 2))
        + ind (decide (c = some 3)) + ind (decide (c = some 4)) + ind (decide (c = some 5))
        + ind (decide (c = some 7)) + ind (decide (c = some 8))
      = ind (decide (Model.kindOf c = Model.Kind.str)) := by
  rw [ind_add_disj (by revert c; decide), ind_add_disj (by revert c; decide),
    ind_add_disj (by revert c; decide), ind_add_disj (by revert c; decide),
    ind_add_disj (by revert c; decide), ind_add_disj (by revert c; decide),
    ind_add_disj (by revert c; decide)]
  congr 1
  revert c; decide

lemma kInt_ind (c : Option Claim) :
    ind (decide (c = some 9)) + ind (decide (c = some 10))
      = ind (decide (Model.kindOf c = Model.Kind.int)) := by
  rw [ind_add_disj (by revert c; decide)]
  congr 1
  revert c; decide

lemma kBool_ind (c : Option Claim) :
    ind (decide (c = some 6)) = ind (decide (Model.kindOf c = Model.Kind.bool)) := by
  congr 1
  revert c; decide

/-! ## The `*Prev` half, read pointwise -/

lemma stPrev_get (hE : EncodesPrev inp r) (j : St) :
    inp.stPrev[j] = ind (decide (r.st = j)) := by
  rw [hE.1 j]
  by_cases h : r.st = j
  · subst h; simp [ind]
  · simp [ind, h, Ne.symm h]

lemma subPrev_get (hE : EncodesPrev inp r) (j : Sub) :
    inp.subPrev[j] = ind (decide (r.sub = j)) := by
  rw [hE.2.1 j]
  by_cases h : r.sub = j
  · subst h; simp [ind]
  · simp [ind, h, Ne.symm h]

lemma mPrev_get (hE : EncodesPrev inp r) (k : Claim) : inp.mPrev[k] = ind r.m[k] := by
  rw [hE.2.2.2.2.1 k]
  cases h : r.m[k] <;> simp [ind, h]

lemma claimPrev_get (hE : EncodesPrev inp r) (k : Claim) :
    inp.claimPrev[k] = ind (decide (r.claim = some k)) := by
  rw [hE.2.2.2.2.2.1 k]
  by_cases h : r.claim = some k
  · simp [ind, h]
  · simp [ind, h]

/-! ## The derived signals -/

lemma inStr_eq (hE : EncodesPrev inp r) : inStr inp.stPrev = ind (Model.inStr r.st) := by
  simp only [inStr, Fin.getElem_fin, stPrev_get hE St.KEY, stPrev_get hE St.STR, inStr_ind]

lemma closeQuote_eq (hE : EncodesPrev inp r) :
    closeQuote inp.byte inp.subPrev
      = ind ((inp.byte.val == Specs.JSON.quote) && decide (r.sub = Sub.PLAIN)) := by
  simp only [closeQuote, classesOf, Fin.getElem_fin, subPrev_get hE Sub.PLAIN, ind_mul]

lemma inH_eq (hE : EncodesPrev inp r) :
    inH inp.subPrev
      = ind (decide (r.sub = Sub.H1) || decide (r.sub = Sub.H2) || decide (r.sub = Sub.H3)) := by
  simp only [inH, Fin.getElem_fin, subPrev_get hE Sub.H1, subPrev_get hE Sub.H2,
    subPrev_get hE Sub.H3, inH_ind]

lemma inVal_eq (hE : EncodesPrev inp r) : inVal inp.stPrev = ind (inValP r.st) := by
  simp only [inVal, Fin.getElem_fin, stPrev_get hE St.PRE, stPrev_get hE St.OBJ,
    stPrev_get hE St.KEY, stPrev_get hE St.AKEY, stPrev_get hE St.PVAL, stPrev_get hE St.AVAL,
    stPrev_get hE St.SEP, stPrev_get hE St.END, inVal_ind]

/-! ## The kind gates -/

lemma kStr_eq (hE : EncodesPrev inp r) :
    kStr inp.claimPrev = ind (decide (Model.kindOf r.claim = Model.Kind.str)) := by
  have h0 : inp.claimPrev[0] = ind (decide (r.claim = some 0)) := claimPrev_get hE 0
  have h1 : inp.claimPrev[1] = ind (decide (r.claim = some 1)) := claimPrev_get hE 1
  have h2 : inp.claimPrev[2] = ind (decide (r.claim = some 2)) := claimPrev_get hE 2
  have h3 : inp.claimPrev[3] = ind (decide (r.claim = some 3)) := claimPrev_get hE 3
  have h4 : inp.claimPrev[4] = ind (decide (r.claim = some 4)) := claimPrev_get hE 4
  have h5 : inp.claimPrev[5] = ind (decide (r.claim = some 5)) := claimPrev_get hE 5
  have h7 : inp.claimPrev[7] = ind (decide (r.claim = some 7)) := claimPrev_get hE 7
  have h8 : inp.claimPrev[8] = ind (decide (r.claim = some 8)) := claimPrev_get hE 8
  simp only [kStr, h0, h1, h2, h3, h4, h5, h7, h8, kStr_ind]

lemma kInt_eq (hE : EncodesPrev inp r) :
    kInt inp.claimPrev = ind (decide (Model.kindOf r.claim = Model.Kind.int)) := by
  have h9 : inp.claimPrev[9] = ind (decide (r.claim = some 9)) := claimPrev_get hE 9
  have h10 : inp.claimPrev[10] = ind (decide (r.claim = some 10)) := claimPrev_get hE 10
  simp only [kInt, h9, h10, kInt_ind]

lemma kBool_eq (hE : EncodesPrev inp r) :
    kBool inp.claimPrev = ind (decide (Model.kindOf r.claim = Model.Kind.bool)) := by
  have h6 : inp.claimPrev[6] = ind (decide (r.claim = some 6)) := claimPrev_get hE 6
  simp only [kBool, h6, kBool_ind]

lemma kUnk_eq (hE : EncodesPrev inp r) :
    kUnk inp.claimPrev = ind (decide (Model.kindOf r.claim = Model.Kind.unk)) := by
  simp only [kUnk, kStr_eq hE, kInt_eq hE, kBool_eq hE]
  cases Model.kindOf r.claim <;> simp [ind]

lemma kinds_eq (hE : EncodesPrev inp r) :
    kinds inp.claimPrev = AutomatonModel.kindsOf (Model.kindOf r.claim) := by
  simp only [kinds, AutomatonModel.kindsOf, kStr_eq hE, kInt_eq hE, kBool_eq hE, kUnk_eq hE]

/-! ## The four emission flags -/

lemma sub_state_disj {p q : Sub} (h : p ≠ q) (sb : Sub) (i x y : Bool) :
    ((i && decide (sb = p) && x) && (i && decide (sb = q) && y)) = false := by
  by_cases h1 : sb = p
  · subst h1; simp [h]
  · simp [h1]

/-- The `emitPlain` flag of `Model.signals`. -/
def emitPlainB (r : Regs) (b : ℕ) : Bool :=
  Model.inStr r.st && decide (r.sub = Sub.PLAIN) && Model.isUnescaped b
/-- The `emitEsc` flag of `Model.signals`. -/
def emitEscB (r : Regs) (b : ℕ) : Bool :=
  Model.inStr r.st && decide (r.sub = Sub.ESC) && Model.isSimpleEsc b
/-- The `emitU` flag of `Model.signals`. -/
def emitUB (r : Regs) (b : ℕ) : Bool :=
  Model.inStr r.st && decide (r.sub = Sub.H4) && Model.isHex b
/-- The `emitUtf8` flag of `Model.signals`. -/
def emitUtf8B (r : Regs) (b : ℕ) : Bool :=
  Model.inStr r.st && decide (r.sub = Sub.C1) && Model.isCont b

lemma sig_emit (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').emit
      = (emitPlainB r b || emitEscB r b || emitUB r b || emitUtf8B r b) := rfl

lemma sig_cp (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').cp
      = (if emitPlainB r b then b else if emitEscB r b then Model.escVal b
         else if emitUB r b then 16 * r.hexAcc + Model.hexVal b
         else if emitUtf8B r b then Model.nonAsciiMarker else 0) := rfl

lemma emitPlain_eq (hE : EncodesPrev inp r) :
    emitPlain inp.byte inp.stPrev inp.subPrev = ind (emitPlainB r inp.byte.val) := by
  simp only [emitPlain, emitPlainB, classesOf, Fin.getElem_fin, inStr_eq hE,
    subPrev_get hE Sub.PLAIN, ind_mul]

lemma emitEsc_eq (hE : EncodesPrev inp r) :
    emitEsc inp.byte inp.stPrev inp.subPrev = ind (emitEscB r inp.byte.val) := by
  simp only [emitEsc, emitEscB, classesOf, Fin.getElem_fin, inStr_eq hE,
    subPrev_get hE Sub.ESC, ind_mul]

lemma emitU_eq (hE : EncodesPrev inp r) :
    emitU inp.byte inp.stPrev inp.subPrev = ind (emitUB r inp.byte.val) := by
  simp only [emitU, emitUB, classesOf, Fin.getElem_fin, inStr_eq hE,
    subPrev_get hE Sub.H4, ind_mul]

lemma emitUtf8_eq (hE : EncodesPrev inp r) :
    emitUtf8 inp.byte inp.stPrev inp.subPrev = ind (emitUtf8B r inp.byte.val) := by
  simp only [emitUtf8, emitUtf8B, classesOf, Fin.getElem_fin, inStr_eq hE,
    subPrev_get hE Sub.C1, ind_mul]

lemma emit_eq (hE : EncodesPrev inp r) (st' : St) :
    emit inp.byte inp.stPrev inp.subPrev = ind (Model.signals r inp.byte.val st').emit := by
  have d12 := sub_state_disj (p := Sub.PLAIN) (q := Sub.ESC) (by decide) r.sub
  have d13 := sub_state_disj (p := Sub.PLAIN) (q := Sub.H4) (by decide) r.sub
  have d14 := sub_state_disj (p := Sub.PLAIN) (q := Sub.C1) (by decide) r.sub
  have d23 := sub_state_disj (p := Sub.ESC) (q := Sub.H4) (by decide) r.sub
  have d24 := sub_state_disj (p := Sub.ESC) (q := Sub.C1) (by decide) r.sub
  have d34 := sub_state_disj (p := Sub.H4) (q := Sub.C1) (by decide) r.sub
  simp only [emit, emitPlain_eq hE, emitEsc_eq hE, emitU_eq hE, emitUtf8_eq hE, sig_emit,
    emitPlainB, emitEscB, emitUB, emitUtf8B]
  rw [ind_add_disj (d12 _ _ _), ind_add_disj (ByteClass.or_disj (d13 _ _ _) (d23 _ _ _)),
    ind_add_disj (ByteClass.or_disj (ByteClass.or_disj (d14 _ _ _) (d24 _ _ _)) (d34 _ _ _))]

/-! ## The hex digit, the escape value and the decoded code point -/

lemma byte_cast (inp : Inputs (F circomPrime)) :
    ((inp.byte.val : ℕ) : F circomPrime) = inp.byte := by rw [ZMod.natCast_val, ZMod.cast_id]

lemma hexVal_eq (inp : Inputs (F circomPrime)) :
    hexVal inp.byte = ((Model.hexVal inp.byte.val : ℕ) : F circomPrime) := by
  have hb := byte_cast inp
  rcases hex_classes inp.byte.val with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ |
    ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩
  · have : Model.hexVal inp.byte.val = inp.byte.val - 48 := by
      simp only [Model.hexVal, h1, if_true, Specs.JSON.digit0]
    rw [this, Nat.cast_sub h4, hb]
    simp only [hexVal, classesOf, h1, h2, h3, ind]
    push_cast
    ring
  · have : Model.hexVal inp.byte.val = inp.byte.val - 55 := by
      simp only [Model.hexVal, h1, h2, if_true, if_false, Bool.false_eq_true,
        Specs.JSON.upperA]
      omega
    rw [this, Nat.cast_sub (by omega), hb]
    simp only [hexVal, classesOf, h1, h2, h3, ind]
    push_cast
    ring
  · have : Model.hexVal inp.byte.val = inp.byte.val - 87 := by
      simp only [Model.hexVal, h1, h2, h3, if_true, if_false, Bool.false_eq_true,
        Specs.JSON.lowerA]
      omega
    rw [this, Nat.cast_sub (by omega), hb]
    simp only [hexVal, classesOf, h1, h2, h3, ind]
    push_cast
    ring
  · have : Model.hexVal inp.byte.val = 0 := by
      simp only [Model.hexVal, h1, h2, h3, if_false, Bool.false_eq_true]
    rw [this]
    simp only [hexVal, classesOf, h1, h2, h3, ind]
    push_cast
    ring

lemma escVal_eq (inp : Inputs (F circomPrime)) :
    escVal inp.byte = ((Model.escVal inp.byte.val : ℕ) : F circomPrime) := by
  simp only [escVal, classesOf, ind, Model.escVal, Specs.JSON.quote, Specs.JSON.backslash,
    Specs.JSON.slash, Specs.JSON.lowerB, Specs.JSON.lowerF, Specs.JSON.lowerN,
    Specs.JSON.lowerR, Specs.JSON.lowerT, Specs.JSON.backspace, Specs.JSON.formfeed,
    Specs.JSON.lf, Specs.JSON.cr, Specs.JSON.tab]
  by_cases h1 : inp.byte.val = 0x22
  · simp [h1]
  by_cases h2 : inp.byte.val = 0x5C
  · simp [h1, h2]
  by_cases h3 : inp.byte.val = 0x2F
  · simp [h1, h2, h3]
  by_cases h4 : inp.byte.val = 0x62
  · simp [h1, h2, h3, h4]
  by_cases h5 : inp.byte.val = 0x66
  · simp [h1, h2, h3, h4, h5]
  by_cases h6 : inp.byte.val = 0x6E
  · simp [h1, h2, h3, h4, h5, h6]
  by_cases h7 : inp.byte.val = 0x72
  · simp [h1, h2, h3, h4, h5, h6, h7]
  by_cases h8 : inp.byte.val = 0x74
  · simp [h1, h2, h3, h4, h5, h6, h7, h8]
  · simp [h1, h2, h3, h4, h5, h6, h7, h8]


/-- The decoded code point of a position, as a field element. -/
lemma cp_eq (hE : EncodesPrev inp r) (st' : St) :
    cp inp.byte inp.stPrev inp.subPrev inp.hexAccPrev
      = (((Model.signals r inp.byte.val st').cp : ℕ) : F circomPrime) := by
  have hb := byte_cast inp
  have hh : inp.hexAccPrev = ((r.hexAcc : ℕ) : F circomPrime) := hE.2.2.1
  simp only [cp, emitPlain_eq hE, emitEsc_eq hE, emitU_eq hE, emitUtf8_eq hE, escVal_eq,
    hexVal_eq, sig_cp, hh, emitPlainB, emitEscB, emitUB, emitUtf8B]
  by_cases hi : Model.inStr r.st = true
  · simp only [hi, Bool.true_and]
    by_cases hp : r.sub = Sub.PLAIN
    · simp +decide [ind, hp, hb, Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1]
    · by_cases he : r.sub = Sub.ESC
      · simp +decide [ind, hp, he, Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1]
      · by_cases h4 : r.sub = Sub.H4
        · simp +decide [ind, hp, he, h4, Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1]
        · by_cases hc : r.sub = Sub.C1
          · simp +decide [ind, hp, he, h4, hc, Model.nonAsciiMarker,
              Sub.PLAIN, Sub.ESC, Sub.H4, Sub.C1]
          · simp +decide [ind, hp, he, h4, hc]
  · have hi' : Model.inStr r.st = false := by simpa using hi
    simp only [hi']
    simp [ind]

/-- The code point of a position is below `2 ^ 16` (the model-side bound). -/
lemma sig_cp_lt (r : Regs) {b : ℕ} (hb : b < 256) (hh : r.hexAcc < 4096) (st' : St) :
    (Model.signals r b st').cp < 65536 := by
  rw [sig_cp]
  have h1 : Model.hexVal b < 16 := by
    simp only [Model.hexVal, Model.isDigit, Model.isUpperHex, Model.isLowerHex,
      Specs.JSON.digit0, Specs.JSON.digit9, Specs.JSON.upperA, Specs.JSON.upperF,
      Specs.JSON.lowerA, Specs.JSON.lowerF, Bool.and_eq_true, decide_eq_true_eq]
    split_ifs <;> omega
  have h2 : Model.escVal b < 256 := by
    simp only [Model.escVal, Specs.JSON.quote, Specs.JSON.backslash, Specs.JSON.slash,
      Specs.JSON.backspace, Specs.JSON.formfeed, Specs.JSON.lf, Specs.JSON.cr, Specs.JSON.tab]
    split_ifs <;> omega
  simp only [Model.nonAsciiMarker]
  split_ifs <;> omega

/-! ## The key events and the matchers -/

/-- The `keyClose` flag of `Model.signals`. -/
def keyCloseB (r : Regs) (b : ℕ) : Bool :=
  decide (r.st = St.KEY) && (b == Specs.JSON.quote) && decide (r.sub = Sub.PLAIN)

lemma sig_keyClose (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').keyClose = keyCloseB r b := rfl

lemma sig_match (r : Regs) (b : ℕ) (st' : St) (k : Claim) :
    (Model.signals r b st').match_[k]
      = (keyCloseB r b && r.m[k] && decide (r.kIdx = (Model.claimName k).length)) := by
  simp [Model.signals, keyCloseB]

lemma keyClose_eq (hE : EncodesPrev inp r) :
    keyClose inp.byte inp.stPrev inp.subPrev = ind (keyCloseB r inp.byte.val) := by
  simp only [keyClose, keyCloseB, closeQuote_eq hE, Fin.getElem_fin, stPrev_get hE St.KEY,
    ind_mul, Bool.and_assoc]

lemma kIdxOH_get (hE : EncodesPrev inp r) (hk : r.kIdx < kIdxMax) (t : ℕ) (ht : t < kIdxMax) :
    (ohOf kIdxMax inp.kIdxPrev)[t]'ht = ind (decide (t = r.kIdx)) := by
  have hp : r.kIdx < circomPrime := by
    have : (16 : ℕ) < circomPrime := by decide
    simp only [Model.kIdxMax] at hk; omega
  simp only [ohOf, Vector.getElem_ofFn, hE.2.2.2.1, ZMod.val_natCast_of_lt hp]
  by_cases h : t = r.kIdx
  · simp [ind, h]
  · simp [ind, h]

lemma kIdxOH_getF (hE : EncodesPrev inp r) (hk : r.kIdx < kIdxMax) (t : Fin kIdxMax) :
    (ohOf kIdxMax inp.kIdxPrev)[t] = ind (decide (t.val = r.kIdx)) :=
  kIdxOH_get hE hk t.val t.isLt

lemma expected_eq (hE : EncodesPrev inp r) (hk : r.kIdx < kIdxMax) (k : Claim) :
    Matcher.expected k (ohOf kIdxMax inp.kIdxPrev)
      = ((Model.nameAt k r.kIdx : ℕ) : F circomPrime) := by
  simp only [Matcher.expected, foldl_add_eq_sum, Fin.getElem_fin]
  rw [Finset.sum_eq_single (⟨r.kIdx, hk⟩ : Fin kIdxMax)]
  · simp only [Fin.val_mk, kIdxOH_get hE hk r.kIdx hk]
    simp [ind]
  · intro t _ ht
    simp only [kIdxOH_get hE hk t.val t.isLt]
    have hne : ¬ (t.val = r.kIdx) := fun h => ht (Fin.ext h)
    simp [ind, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma matchOf_eq (hE : EncodesPrev inp r) (hk : r.kIdx < kIdxMax) (st' : St) (k : Claim) :
    matchOf k inp.byte inp.stPrev inp.subPrev inp.mPrev inp.kIdxPrev
      = ind ((Model.signals r inp.byte.val st').match_[k]) := by
  simp only [matchOf, sig_match, keyClose_eq hE, mPrev_get hE k, kIdxOH_getF hE hk, kLen,
    Fin.val_mk, ind_mul]
  have hsym : decide ((Model.claimName k).length = r.kIdx)
      = decide (r.kIdx = (Model.claimName k).length) := decide_eq_decide.mpr eq_comm
  congr 1
  simp only [hsym, Bool.and_assoc]


/-! ## The value signals -/

/-- The `strEmit` flag of `Model.signals`. -/
def strEmitB (r : Regs) (b : ℕ) : Bool :=
  (Model.signals r b r.st).emit && decide (r.st = St.STR)
/-- The `digitEmit` flag of `Model.signals`. -/
def digitEmitB (r : Regs) (b : ℕ) : Bool :=
  Model.isDigit b && (decide (r.st = St.PVAL) || decide (r.st = St.NSIGN) ||
    decide (r.st = St.NINT))

lemma sig_vEmit (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').vEmit = (strEmitB r b || digitEmitB r b) := rfl

lemma sig_write (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').write
      = ((strEmitB r b || digitEmitB r b) &&
          (decide (Model.kindOf r.claim = Model.Kind.str) ||
            decide (Model.kindOf r.claim = Model.Kind.int))) := rfl

lemma sig_valOut (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').valOut
      = (if strEmitB r b then (Model.signals r b st').cp
         else if digitEmitB r b then b - Specs.JSON.digit0 else 0) := rfl

lemma sig_minusFlag (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').minusFlag
      = (decide (r.st = St.PVAL) && (b == Specs.JSON.minus)) := rfl

lemma sig_trueDone (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').trueDone
      = (decide (r.st = St.T3) && (b == Specs.JSON.lowerE)) := rfl

lemma strEmit_eq (hE : EncodesPrev inp r) :
    strEmit inp.byte inp.stPrev inp.subPrev = ind (strEmitB r inp.byte.val) := by
  simp only [strEmit, strEmitB, emit_eq hE r.st, Fin.getElem_fin, stPrev_get hE St.STR, ind_mul]

lemma digitEmit_ind (s : St) :
    ind (decide (s = St.PVAL)) + ind (decide (s = St.NSIGN)) + ind (decide (s = St.NINT))
      = ind (decide (s = St.PVAL) || decide (s = St.NSIGN) || decide (s = St.NINT)) := by
  rw [ind_add_disj (by revert s; decide), ind_add_disj (by revert s; decide)]

lemma digitEmit_eq (hE : EncodesPrev inp r) :
    digitEmit inp.byte inp.stPrev = ind (digitEmitB r inp.byte.val) := by
  simp only [digitEmit, digitEmitB, classesOf, Fin.getElem_fin, stPrev_get hE St.PVAL,
    stPrev_get hE St.NSIGN, stPrev_get hE St.NINT, digitEmit_ind, ind_mul]

lemma vEmit_eq (hE : EncodesPrev inp r) (st' : St) :
    vEmit inp.byte inp.stPrev inp.subPrev = ind ((Model.signals r inp.byte.val st').vEmit) := by
  have hd : (strEmitB r inp.byte.val && digitEmitB r inp.byte.val) = false := by
    simp only [strEmitB, digitEmitB, Bool.and_eq_false_iff]
    by_cases h : r.st = St.STR
    · right; simp +decide [h, St.STR, St.PVAL, St.NSIGN, St.NINT]
    · left; simp [h]
  simp only [vEmit, strEmit_eq hE, digitEmit_eq hE, sig_vEmit, ind_add_disj hd]

lemma write_eq (hE : EncodesPrev inp r) (st' : St) :
    write inp.byte inp.stPrev inp.subPrev inp.claimPrev
      = ind ((Model.signals r inp.byte.val st').write) := by
  have hd : (decide (Model.kindOf r.claim = Model.Kind.str) &&
      decide (Model.kindOf r.claim = Model.Kind.int)) = false := by
    cases Model.kindOf r.claim <;> simp
  simp only [write, vEmit_eq hE st', kStr_eq hE, kInt_eq hE, ind_add_disj hd, sig_write,
    sig_vEmit, ind_mul]

lemma minusFlag_eq (hE : EncodesPrev inp r) (st' : St) :
    minusFlag inp.byte inp.stPrev = ind ((Model.signals r inp.byte.val st').minusFlag) := by
  simp only [minusFlag, classesOf, sig_minusFlag, Fin.getElem_fin, stPrev_get hE St.PVAL,
    ind_mul]

lemma trueDone_eq (hE : EncodesPrev inp r) (st' : St) :
    trueDone inp.byte inp.stPrev = ind ((Model.signals r inp.byte.val st').trueDone) := by
  simp only [trueDone, classesOf, sig_trueDone, Fin.getElem_fin, stPrev_get hE St.T3, ind_mul]

lemma valOut_eq (hE : EncodesPrev inp r) (st' : St) :
    valOut inp.byte inp.stPrev inp.subPrev inp.hexAccPrev
      = (((Model.signals r inp.byte.val st').valOut : ℕ) : F circomPrime) := by
  have hb := byte_cast inp
  simp only [valOut, strEmit_eq hE, digitEmit_eq hE, cp_eq hE st', sig_valOut]
  by_cases hs : strEmitB r inp.byte.val = true
  · have hd : digitEmitB r inp.byte.val = false := by
      simp only [strEmitB, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp +decide [digitEmitB, hs.2, St.STR, St.PVAL, St.NSIGN, St.NINT]
    simp [ind, hs, hd]
  · have hs' : strEmitB r inp.byte.val = false := by simpa using hs
    by_cases hd : digitEmitB r inp.byte.val = true
    · have hdg : Specs.JSON.digit0 ≤ inp.byte.val := by
        simp only [digitEmitB, Bool.and_eq_true, Model.isDigit, Specs.JSON.digit0,
          Specs.JSON.digit9, decide_eq_true_eq] at hd
        simp only [Specs.JSON.digit0]
        omega
      simp only [hs', hd, ind, Bool.false_eq_true, if_false, if_true, zero_mul, one_mul,
        zero_add]
      rw [Nat.cast_sub hdg, hb]
      norm_num [Specs.JSON.digit0]
    · have hd' : digitEmitB r inp.byte.val = false := by simpa using hd
      simp [ind, hs', hd']


/-! ## Casting small naturals -/

lemma cast_inj {x y : ℕ} (hx : x < circomPrime) (hy : y < circomPrime) :
    ((x : F circomPrime) = (y : F circomPrime)) ↔ x = y := by
  constructor
  · intro h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] at this
  · intro h; rw [h]

lemma claimName_lt (k : Claim) : ∀ x ∈ Model.claimName k, x < 256 := by revert k; decide

lemma nameAt_lt (k : Claim) (t : ℕ) : Model.nameAt k t < circomPrime := by
  have hp : (2 ^ 20 : ℕ) < circomPrime := by decide
  simp only [Model.nameAt, List.getD]
  rcases h : (Model.claimName k)[t]? with _ | x
  · simp only [Option.getD, Model.impossible]; omega
  · simp only [Option.getD]
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp h
    have := claimName_lt k x (h2 ▸ List.getElem_mem h1)
    omega

/-! ## The ASCII test and the matcher comparison -/

lemma ltAscii_eq (hE : EncodesPrev inp r) (hb : inp.byte.val < 256) (hh : r.hexAcc < 4096)
    (st' : St) :
    ltAscii inp.byte inp.stPrev inp.subPrev inp.hexAccPrev
      = ind (decide ((Model.signals r inp.byte.val st').cp < 128)) := by
  have hlt := sig_cp_lt r hb hh st'
  have hp : (Model.signals r inp.byte.val st').cp < circomPrime := by
    have : (65536 : ℕ) < circomPrime := by decide
    omega
  simp only [ltAscii, cp_eq hE st', ZMod.val_natCast_of_lt hp]
  by_cases h : (Model.signals r inp.byte.val st').cp < 128
  · simp [ind, h]
  · simp [ind, h]

lemma eqCp_eq (hE : EncodesPrev inp r) (hb : inp.byte.val < 256) (hw : WFRegs r) (st' : St)
    (k : Claim) :
    eqCp k inp.byte inp.stPrev inp.subPrev inp.hexAccPrev inp.kIdxPrev
      = ind (decide ((Model.signals r inp.byte.val st').cp = Model.nameAt k r.kIdx)) := by
  have hlt := sig_cp_lt r hb hw.1 st'
  have hp : (Model.signals r inp.byte.val st').cp < circomPrime := by
    have : (65536 : ℕ) < circomPrime := by decide
    omega
  simp only [eqCp, cp_eq hE st', expected_eq hE hw.2.1 k,
    cast_inj hp (nameAt_lt k r.kIdx)]
  by_cases h : (Model.signals r inp.byte.val st').cp = Model.nameAt k r.kIdx
  · simp [ind, h]
  · simp [ind, h]

/-! ## The routed cell -/

lemma ofsOH_get (hE : EncodesPrev inp r) (ho : r.ofs < ofsMax) (t : ℕ) (ht : t < ofsMax) :
    (ohOf ofsMax inp.ofsPrev)[t]'ht = ind (decide (t = r.ofs)) := by
  have hp : r.ofs < circomPrime := by
    have : (129 : ℕ) < circomPrime := by decide
    simp only [Model.ofsMax] at ho; omega
  simp only [ohOf, Vector.getElem_ofFn, hE.2.2.2.2.2.2.1, ZMod.val_natCast_of_lt hp]
  by_cases h : t = r.ofs
  · simp [ind, h]
  · simp [ind, h]

lemma slotEx_eq (hE : EncodesPrev inp r) (ho : r.ofs < ofsMax) (n : ℕ) (hn : n ≤ ofsMax) :
    slotEx n hn (ohOf ofsMax inp.ofsPrev) = ind (decide (r.ofs < n)) := by
  simp only [slotEx, RouteSlot.ofsAt, foldl_add_eq_sum]
  by_cases h : r.ofs < n
  · rw [Finset.sum_eq_single (⟨r.ofs, h⟩ : Fin n)]
    · rw [ofsOH_get hE ho r.ofs (lt_of_lt_of_le h hn)]
      simp [ind, h]
    · intro t _ ht
      rw [ofsOH_get hE ho t.val (lt_of_lt_of_le t.isLt hn)]
      have hne : ¬ (t.val = r.ofs) := fun hh => ht (Fin.ext hh)
      simp [ind, hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [Finset.sum_eq_zero, ind]
    · simp [h]
    · intro t _
      rw [ofsOH_get hE ho t.val (lt_of_lt_of_le t.isLt hn)]
      have hne : ¬ (t.val = r.ofs) := fun hh => h (hh ▸ t.isLt)
      simp [ind, hne]

lemma slotSel_eq (hE : EncodesPrev inp r) (ho : r.ofs < ofsMax) (n : ℕ) (hn : n ≤ ofsMax)
    (cells : Vector (F circomPrime) n) (h : r.ofs < n) :
    slotSel n hn (ohOf ofsMax inp.ofsPrev) cells = cells[r.ofs]'h := by
  simp only [slotSel, RouteSlot.ofsAt, foldl_add_eq_sum]
  rw [Finset.sum_eq_single (⟨r.ofs, h⟩ : Fin n)]
  · rw [ofsOH_get hE ho r.ofs (lt_of_lt_of_le h hn)]
    simp [ind]
  · intro t _ ht
    rw [ofsOH_get hE ho t.val (lt_of_lt_of_le t.isLt hn)]
    have hne : ¬ (t.val = r.ofs) := fun hh => ht (Fin.ext hh)
    simp [ind, hne]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

lemma claimPrev_all (hE : EncodesPrev inp r) :
    inp.claimPrev[0] = ind (decide (r.claim = some 0)) ∧
    inp.claimPrev[1] = ind (decide (r.claim = some 1)) ∧
    inp.claimPrev[2] = ind (decide (r.claim = some 2)) ∧
    inp.claimPrev[3] = ind (decide (r.claim = some 3)) ∧
    inp.claimPrev[4] = ind (decide (r.claim = some 4)) ∧
    inp.claimPrev[5] = ind (decide (r.claim = some 5)) ∧
    inp.claimPrev[6] = ind (decide (r.claim = some 6)) ∧
    inp.claimPrev[7] = ind (decide (r.claim = some 7)) ∧
    inp.claimPrev[8] = ind (decide (r.claim = some 8)) ∧
    inp.claimPrev[9] = ind (decide (r.claim = some 9)) ∧
    inp.claimPrev[10] = ind (decide (r.claim = some 10)) :=
  ⟨claimPrev_get hE 0, claimPrev_get hE 1, claimPrev_get hE 2, claimPrev_get hE 3,
    claimPrev_get hE 4, claimPrev_get hE 5, claimPrev_get hE 6, claimPrev_get hE 7,
    claimPrev_get hE 8, claimPrev_get hE 9, claimPrev_get hE 10⟩

lemma claimCap_eq (k : Claim) :
    Model.claimCap k = ([32, 32, 128, 128, 64, 128, 0, 64, 64, 12, 12] : List ℕ).getD k.val 0 := by
  revert k; decide

lemma slot_cell {n : ℕ} (hn : n ≤ ofsMax) (cells : Vector (F circomPrime) n)
    (hE : EncodesPrev inp r) (ho : r.ofs < ofsMax) (h : r.ofs < n) :
    slotSel n hn (ohOf ofsMax inp.ofsPrev) cells = cells[r.ofs]?.getD 0 := by
  rw [slotSel_eq hE ho n hn cells h, Vector.getElem?_eq_getElem h]
  rfl

lemma existsIn_some (hE : EncodesPrev inp r) (ho : r.ofs < ofsMax) (k : Claim)
    (hc : r.claim = some k) :
    existsIn inp.claimPrev inp.ofsPrev = ind (decide (r.ofs < Model.claimCap k)) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := claimPrev_all hE
  simp only [existsIn, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hc,
    slotEx_eq hE ho, ind_mul, claimCap_eq]
  fin_cases k <;> simp +decide [ind]

lemma selected_eq (hE : EncodesPrev inp r) (ho : r.ofs < ofsMax) (k : Claim)
    (hc : r.claim = some k) (hlt : r.ofs < Model.claimCap k) :
    selected inp.claimPrev inp.ofsPrev inp.out = outCell inp.out k r.ofs := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := claimPrev_all hE
  rw [claimCap_eq] at hlt
  simp only [selected, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hc, outCell]
  fin_cases k <;> simp +decide only [ind, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD, Fin.isValue, Fin.val_mk, decide_true, decide_false,
      Bool.false_eq_true, if_true, if_false, one_mul, zero_mul, add_zero, zero_add,
      reduceIte] at hlt ⊢ <;>
    first
      | exact absurd hlt (by omega)
      | exact slot_cell _ _ hE ho (by omega)

/-! ## The model's step, field by field -/

lemma sig_hexVal (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').hexVal = Model.hexVal b := rfl

/-- `if c then none else some x = some y` forces `y = x`. -/
private theorem ite_none_some {α : Type} (c : Prop) [Decidable c] (x y : α)
    (h : (if c then none else some x) = some y) : y = x := by
  split at h
  · exact absurd h (by simp)
  · exact (Option.some.inj h).symm

lemma step_fields {r r' : Regs} {b : ℕ} (h : Model.step r b = some r') :
    Model.stepSub (Model.inStr r.st) r.sub b = some r'.sub ∧
    Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b = some r'.st ∧
    r'.hexAcc = (if (decide (r.sub = Sub.H1) || decide (r.sub = Sub.H2) ||
      decide (r.sub = Sub.H3)) then 16 * r.hexAcc + Model.hexVal b else 0) ∧
    r'.kIdx = (if r.st = St.KEY then
      min (r.kIdx + (if (Model.signals r b r'.st).emit then 1 else 0)) (kIdxMax - 1) else 0) ∧
    r'.claim = (if (Model.signals r b r'.st).keyClose then
        (List.finRange nClaims).find? (fun k => (Model.signals r b r'.st).match_[k])
      else if (Model.signals r b r'.st).keyStart then none else r.claim) ∧
    r'.ofs = min ((if inValP r.st then r.ofs else 0)
      + (if (Model.signals r b r'.st).vEmit then 1 else 0)) (ofsMax - 1) ∧
    r'.nMem = r.nMem + (if (Model.signals r b r'.st).keyStart then 1 else 0) ∧
    (∀ k : Claim, r'.m[k] = (if (Model.signals r b r'.st).keyStart then true
      else if r.st = St.KEY then r.m[k] && (!(Model.signals r b r'.st).emit ||
        decide ((Model.signals r b r'.st).cp = Model.nameAt k r.kIdx)) else false)) := by
  simp only [Model.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨sub', hsub, st', hst, h⟩ := h
  have hr' := ite_none_some _ _ _ h
  subst hr'
  refine ⟨hsub, hst, ?_, ?_, ?_, ?_, ?_, fun k => ?_⟩ <;> simp [inValP, sig_hexVal]

lemma step_isSome_of {r : Regs} {b : ℕ} {sub' : Sub} {st' : St}
    (hsub : Model.stepSub (Model.inStr r.st) r.sub b = some sub')
    (hst : Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st b = some st')
    (hcap : (Model.signals r b st').write = true →
      ∀ k : Claim, r.claim = some k → r.ofs < Model.claimCap k)
    (hascii : (Model.signals r b st').write = true → r.st = St.STR →
      (Model.signals r b st').cp < 0x80) :
    (Model.step r b).isSome := by
  simp only [Model.step, Option.bind_eq_bind, hsub, hst, Option.bind]
  by_cases hw : (Model.signals r b st').write = true
  · rcases hcl : r.claim with _ | k
    · simp [hw, hcl]
      exact hascii hw
    · by_cases hs : r.st = St.STR
      · simp [hw, hcl, hs, hcap hw k hcl, hascii hw hs]
      · simp [hw, hcl, hs, hcap hw k hcl]
  · simp only [Bool.not_eq_true] at hw
    simp [hw]

/-! ## The one-hot source vectors -/

lemma stPrev_ohOf (hE : EncodesPrev inp r) :
    inp.stPrev = ohOf nSt ((r.st.val : ℕ) : F circomPrime) := by
  rw [AutomatonModel.ohOf_eq_ohFin (ByteClass.lt_circomPrime (by norm_num)) r.st]
  refine Vector.ext fun i hi => ?_
  have := hE.1 ⟨i, hi⟩
  simp only [Fin.getElem_fin] at this
  rw [this]
  simp [AutomatonModel.ohFin]

lemma subPrev_ohOf (hE : EncodesPrev inp r) :
    inp.subPrev = ohOf nSub ((r.sub.val : ℕ) : F circomPrime) := by
  rw [AutomatonModel.ohOf_eq_ohFin (ByteClass.lt_circomPrime (by norm_num)) r.sub]
  refine Vector.ext fun i hi => ?_
  have := hE.2.1 ⟨i, hi⟩
  simp only [Fin.getElem_fin] at this
  rw [this]
  simp [AutomatonModel.ohFin]


/-! ## At most one claim matches a closing key -/

lemma claimName_inj : ∀ k k' : Claim, Model.claimName k = Model.claimName k' → k = k' := by decide

lemma match_unique (hinv : MatchInv r) {b : ℕ} {st' : St} {k k' : Claim}
    (hk : (Model.signals r b st').match_[k] = true)
    (hk' : (Model.signals r b st').match_[k'] = true) : k = k' := by
  rw [sig_match] at hk hk'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk hk'
  obtain ⟨⟨-, hmk⟩, hlk⟩ := hk
  obtain ⟨⟨-, hmk'⟩, hlk'⟩ := hk'
  refine claimName_inj k k' ?_
  have hlen : (Model.claimName k).length = (Model.claimName k').length := by omega
  apply List.ext_getElem hlen
  intro n h1 h2
  have hn := hinv k k' hmk hmk' n (by omega)
  simpa only [Model.nameAt, List.getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD] using hn

lemma find_match (hinv : MatchInv r) (b : ℕ) (st' : St) (k : Claim) :
    decide (((List.finRange nClaims).find? fun j => (Model.signals r b st').match_[j]) = some k)
      = (Model.signals r b st').match_[k] := by
  cases hf : (List.finRange nClaims).find? (fun j => (Model.signals r b st').match_[j]) with
  | none =>
      have hpk : (Model.signals r b st').match_[k] = false := by
        have := List.find?_eq_none.mp hf k (List.mem_finRange k)
        simpa using this
      simp [hpk]
  | some j =>
      have hpj : (Model.signals r b st').match_[j] = true := by
        simpa using (List.find?_eq_some_iff_getElem.mp hf).1
      by_cases hc : (Model.signals r b st').match_[k] = true
      · rw [hc, match_unique hinv hpj hc]; simp
      · simp only [Bool.not_eq_true] at hc
        rw [hc]
        simp only [decide_eq_false_iff_not, Option.some.injEq]
        intro heq
        rw [heq, hc] at hpj
        simp at hpj

/-! ## Small `ind` facts -/

lemma ind_eq_one {P : Bool} (h : ind P = 1) : P = true := by
  cases P
  · exact absurd h.symm (by simpa using one_ne_zero (α := F circomPrime))
  · rfl

lemma ind_mul_one_sub (P : Bool) : ind P * (1 - ind P) = 0 := by cases P <;> simp [ind]

lemma ind_and_prop (c : Bool) (P : Prop) [Decidable P] :
    ind c * ind (decide P) = if c ∧ P then 1 else 0 := by
  cases c <;> by_cases h : P <;> simp [ind, h]

lemma ind_eq_ite (c : Bool) : ind c = if c then (1 : F circomPrime) else 0 := rfl

/-- The one state outside a value at which a value character can be emitted. -/
lemma vEmit_outside_value :
    ∀ s : St, inValP s = false →
      (decide (s = St.STR) || decide (s = St.PVAL) || decide (s = St.NSIGN) ||
        decide (s = St.NINT)) = true → s = St.PVAL := by decide

lemma vEmit_state_aux : ∀ (e dg : Bool) (s : St),
    (e && decide (s = St.STR) || dg && (decide (s = St.PVAL) || decide (s = St.NSIGN) ||
      decide (s = St.NINT))) = true →
    (decide (s = St.STR) || decide (s = St.PVAL) || decide (s = St.NSIGN) ||
      decide (s = St.NINT)) = true := by decide

lemma vEmit_state (r : Regs) (b : ℕ) (st' : St) (h : (Model.signals r b st').vEmit = true) :
    (decide (r.st = St.STR) || decide (r.st = St.PVAL) || decide (r.st = St.NSIGN) ||
      decide (r.st = St.NINT)) = true := by
  rw [sig_vEmit] at h
  simp only [strEmitB, digitEmitB] at h
  exact vEmit_state_aux _ _ _ h


lemma ite_eq_ind {P : Prop} [Decidable P] :
    (if P then (1 : F circomPrime) else 0) = ind (decide P) := by
  by_cases h : P <;> simp [ind, h]

lemma kIdx_update (e : Bool) (kidx : ℕ) (hlt : kidx < kIdxMax) :
    (kidx : F circomPrime) + ind e * (1 - ind (decide (kIdxMax - 1 = kidx)))
      = ((min (kidx + (if e then 1 else 0)) (kIdxMax - 1) : ℕ) : F circomPrime) := by
  simp only [Model.kIdxMax] at hlt ⊢
  cases e
  · rw [show (if (false : Bool) then 1 else 0) = 0 from rfl, Nat.add_zero,
      Nat.min_eq_left (show kidx ≤ 16 - 1 by omega)]
    simp [ind]
  · rw [show (if (true : Bool) then 1 else 0) = 1 from rfl]
    by_cases h15 : 16 - 1 = kidx
    · subst h15; norm_num [ind]
    · rw [show ind (decide (16 - 1 = kidx)) = 0 by simp [ind, h15],
        Nat.min_eq_left (show kidx + 1 ≤ 16 - 1 by omega)]
      push_cast
      simp [ind]

lemma ofs_update (v : Bool) (ofs : ℕ) (hlt : ofs < ofsMax) :
    (ofs : F circomPrime) + ind v * (1 - ind (decide (ofsMax - 1 = ofs)))
      = ((min (ofs + (if v then 1 else 0)) (ofsMax - 1) : ℕ) : F circomPrime) := by
  simp only [Model.ofsMax] at hlt ⊢
  cases v
  · rw [show (if (false : Bool) then 1 else 0) = 0 from rfl, Nat.add_zero,
      Nat.min_eq_left (show ofs ≤ 129 - 1 by omega)]
    simp [ind]
  · rw [show (if (true : Bool) then 1 else 0) = 1 from rfl]
    by_cases h128 : 129 - 1 = ofs
    · subst h128; norm_num [ind]
    · rw [show ind (decide (129 - 1 = ofs)) = 0 by simp [ind, h128],
        Nat.min_eq_left (show ofs + 1 ≤ 129 - 1 by omega)]
      push_cast
      simp [ind]

lemma nMem_update (ks : Bool) (n : ℕ) :
    (n : F circomPrime) + ind ks = ((n + (if ks then 1 else 0) : ℕ) : F circomPrime) := by
  cases ks <;> push_cast <;> simp [ind]


/-! ## The two key events -/

lemma sig_keyStart (r : Regs) (b : ℕ) (st' : St) :
    (Model.signals r b st').keyStart
      = (decide (st' = St.KEY) && decide (r.st ≠ St.KEY)) := rfl

lemma keyStart_ne (r : Regs) (b : ℕ) (st' : St)
    (h : (Model.signals r b st').keyStart = true) : r.st ≠ St.KEY := by
  rw [sig_keyStart] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, decide_not, Bool.not_eq_true'] at h
  simpa using h.2

lemma keyClose_keyStart (r : Regs) (b : ℕ) (st' : St)
    (h : (Model.signals r b st').keyClose = true) : (Model.signals r b st').keyStart = false := by
  rw [sig_keyClose, keyCloseB] at h
  rw [sig_keyStart]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp [h.1.1]

lemma match_of_keyClose_false (r : Regs) (b : ℕ) (st' : St) (k : Claim)
    (h : (Model.signals r b st').keyClose = false) : (Model.signals r b st').match_[k] = false := by
  rw [sig_match]
  rw [sig_keyClose] at h
  simp [h]


/-! ## The register rows at an active position

Each row of `Step.main` sets a `*Next` register to an expression in the `*Prev`
half.  These lemmas evaluate that expression against the model's successor, so
that both directions of the gadget -- soundness, which reads the row, and
completeness, which has to produce it -- share the arithmetic. -/

section Active

variable {inp : Inputs (F circomPrime)} {r r' : Regs}

lemma keyStart_active (hE : EncodesPrev inp r)
    (hst : ∀ j : Fin nSt, inp.stNext[j] = if j = r'.st then 1 else 0) :
    keyStart inp.stPrev inp.stNext
      = ind ((Model.signals r inp.byte.val r'.st).keyStart) := by
  have hnk : decide (r.st ≠ St.KEY) = !decide (r.st = St.KEY) := by
    by_cases h : r.st = St.KEY <;> simp [h]
  rw [keyStart, hst St.KEY, stPrev_get hE St.KEY, sig_keyStart, hnk, ite_eq_ind,
    ByteClass.one_sub_ind, ind_mul]
  congr 2
  by_cases h : r'.st = St.KEY
  · simp [h]
  · simp only [h, decide_false]
    exact decide_eq_false (fun hh : St.KEY = r'.st => h hh.symm)

lemma hexAcc_active (hE : EncodesPrev inp r) (hstep : Model.step r inp.byte.val = some r') :
    inp.hexAccPrev + (1 : F circomPrime) * (inH inp.subPrev * (16 * inp.hexAccPrev
        + hexVal inp.byte) - inp.hexAccPrev)
      = ((r'.hexAcc : ℕ) : F circomPrime) := by
  obtain ⟨-, -, hhx, -, -, -, -, -⟩ := step_fields hstep
  rw [one_mul, inH_eq hE, hE.2.2.1, hexVal_eq, hhx]
  rcases hcond : (decide (r.sub = Sub.H1) || decide (r.sub = Sub.H2) ||
      decide (r.sub = Sub.H3)) with _ | _ <;> simp [ind] <;> push_cast <;> ring

lemma kIdx_active (hE : EncodesPrev inp r) (hw : WFRegs r)
    (hstep : Model.step r inp.byte.val = some r') :
    inp.kIdxPrev + (1 : F circomPrime) * (inp.stPrev[St.KEY] * (inp.kIdxPrev
        + emit inp.byte inp.stPrev inp.subPrev
          * (1 - (ohOf kIdxMax inp.kIdxPrev)[kIdxMax - 1])) - inp.kIdxPrev)
      = ((r'.kIdx : ℕ) : F circomPrime) := by
  obtain ⟨-, -, -, hki, -, -, -, -⟩ := step_fields hstep
  rw [one_mul, stPrev_get hE St.KEY, emit_eq hE r'.st,
    kIdxOH_get hE hw.2.1 (kIdxMax - 1) (by decide), hE.2.2.2.1, hki]
  by_cases hkey : r.st = St.KEY
  · have hup := kIdx_update ((Model.signals r inp.byte.val r'.st).emit) r.kIdx hw.2.1
    rw [if_pos hkey]
    simp only [hkey, decide_true, ByteClass.ind_true, one_mul]
    linear_combination hup
  · rw [if_neg hkey]
    simp [hkey, ind]

lemma m_active (hb : inp.byte.val < 256) (hE : EncodesPrev inp r) (hw : WFRegs r)
    (hstep : Model.step r inp.byte.val = some r')
    (hks : keyStart inp.stPrev inp.stNext
      = ind ((Model.signals r inp.byte.val r'.st).keyStart)) (k : Claim) :
    inp.mPrev[k] + (1 : F circomPrime) * (keyStart inp.stPrev inp.stNext
        + inp.stPrev[St.KEY] * (inp.mPrev[k] * (1 - emit inp.byte inp.stPrev inp.subPrev
          * (1 - eqCp k inp.byte inp.stPrev inp.subPrev inp.hexAccPrev inp.kIdxPrev)))
        - inp.mPrev[k])
      = if r'.m[k] then 1 else 0 := by
  obtain ⟨-, -, -, -, -, -, -, hm⟩ := step_fields hstep
  rw [one_mul, mPrev_get hE k, hks, stPrev_get hE St.KEY, emit_eq hE r'.st,
    eqCp_eq hE hb hw r'.st k, hm k]
  by_cases hkst : (Model.signals r inp.byte.val r'.st).keyStart = true
  · simp [hkst, keyStart_ne r inp.byte.val r'.st hkst, ind]
  · simp only [Bool.not_eq_true] at hkst
    by_cases hkey : r.st = St.KEY
    · rcases hmk : r.m[k] with _ | _ <;>
        rcases he : (Model.signals r inp.byte.val r'.st).emit with _ | _ <;>
        by_cases hcp : (Model.signals r inp.byte.val r'.st).cp = Model.nameAt k r.kIdx <;>
        simp [hkst, hkey, hmk, he, hcp, ind]
    · simp [hkst, hkey, ind]

lemma claim_active (hE : EncodesPrev inp r) (hw : WFRegs r)
    (hstep : Model.step r inp.byte.val = some r')
    (hks : keyStart inp.stPrev inp.stNext
      = ind ((Model.signals r inp.byte.val r'.st).keyStart)) (k : Claim) :
    inp.claimPrev[k] + (1 : F circomPrime)
        * (matchOf k inp.byte inp.stPrev inp.subPrev inp.mPrev inp.kIdxPrev
          + hold inp.byte inp.stPrev inp.stNext inp.subPrev * inp.claimPrev[k]
          - inp.claimPrev[k])
      = if r'.claim = some k then 1 else 0 := by
  obtain ⟨-, -, -, -, hcl, -, -, -⟩ := step_fields hstep
  rw [one_mul, matchOf_eq hE hw.2.1 r'.st k, claimPrev_get hE k, hold, keyClose_eq hE,
    ← sig_keyClose r inp.byte.val r'.st, hks, hcl]
  by_cases hkc : (Model.signals r inp.byte.val r'.st).keyClose = true
  · rw [if_pos hkc, keyClose_keyStart r inp.byte.val r'.st hkc, hkc, ite_eq_ind,
      find_match hw.2.2.2.1 inp.byte.val r'.st k]
    simp only [ByteClass.ind_true, ByteClass.ind_false]
    ring
  · simp only [Bool.not_eq_true] at hkc
    rw [match_of_keyClose_false r inp.byte.val r'.st k hkc, hkc]
    simp only [Bool.false_eq_true, if_false]
    by_cases hkst : (Model.signals r inp.byte.val r'.st).keyStart = true
    · rw [hkst]
      simp only [if_true, ByteClass.ind_true, ByteClass.ind_false]
      rw [show (if (none : Option Claim) = some k then (1 : F circomPrime) else 0) = 0
        from by simp]
      ring
    · simp only [Bool.not_eq_true] at hkst
      rw [hkst]
      simp only [Bool.false_eq_true, if_false, ByteClass.ind_true, ByteClass.ind_false,
        ite_eq_ind]
      ring

lemma ofs_active (hE : EncodesPrev inp r) (hw : WFRegs r)
    (hstep : Model.step r inp.byte.val = some r') :
    inp.ofsPrev + (1 : F circomPrime) * (inVal inp.stPrev * inp.ofsPrev
        + vEmit inp.byte inp.stPrev inp.subPrev * (1 - (ohOf ofsMax inp.ofsPrev)[ofsMax - 1])
        - inp.ofsPrev)
      = ((r'.ofs : ℕ) : F circomPrime) := by
  obtain ⟨-, -, -, -, -, hof, -, -⟩ := step_fields hstep
  rw [one_mul, inVal_eq hE, vEmit_eq hE r'.st,
    ofsOH_get hE hw.2.2.1 (ofsMax - 1) (by decide), hE.2.2.2.2.2.2.1, hof]
  by_cases hiv : inValP r.st = true
  · have hup := ofs_update ((Model.signals r inp.byte.val r'.st).vEmit) r.ofs hw.2.2.1
    simp only [hiv, ByteClass.ind_true, one_mul, if_true]
    linear_combination hup
  · simp only [Bool.not_eq_true] at hiv
    simp only [hiv, ByteClass.ind_false, zero_mul, zero_add, Bool.false_eq_true, if_false]
    by_cases hv : (Model.signals r inp.byte.val r'.st).vEmit = true
    · have hpv : r.st = St.PVAL :=
        vEmit_outside_value r.st hiv (vEmit_state r inp.byte.val r'.st hv)
      have hofs0 : r.ofs = 0 := hw.2.2.2.2.1 hpv
      simp only [hv, hofs0, ByteClass.ind_true, one_mul, if_true]
      norm_num [ind, Model.ofsMax]
    · simp only [Bool.not_eq_true] at hv
      simp [hv, ind]

lemma nMem_active (hE : EncodesPrev inp r) (hstep : Model.step r inp.byte.val = some r')
    (hks : keyStart inp.stPrev inp.stNext
      = ind ((Model.signals r inp.byte.val r'.st).keyStart)) :
    inp.nMemPrev + keyStart inp.stPrev inp.stNext = ((r'.nMem : ℕ) : F circomPrime) := by
  obtain ⟨-, -, -, -, -, -, hnm, -⟩ := step_fields hstep
  rw [hks, hE.2.2.2.2.2.2.2, hnm]
  exact nMem_update _ _

/-! ### The successor registers stay in range even when the step fails

`Main` applies `Step.Spec` at position `i + 1` to refute an all-zero successor
state vector, and for that it must first discharge `Step.Assumptions` there --
the three register bounds.  They are forced by the *rows* of position `i`
whether or not the two automata transition, so they belong in the active branch
of `SpecOf` next to the two `optInd` identities, not behind the
`Model.step r b = some r'` hypothesis. -/

lemma hexVal_lt_16 (b : ℕ) : Model.hexVal b < 16 := by
  unfold Model.hexVal Model.isDigit Model.isUpperHex Model.isLowerHex
  simp only [Specs.JSON.digit0, Specs.JSON.digit9, Specs.JSON.upperA, Specs.JSON.upperF,
    Specs.JSON.lowerA, Specs.JSON.lowerF, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs with h1 h2 h3 <;> omega

lemma hexAccNext_val_lt (hE : EncodesPrev inp r) (hcap : r.hexAcc < hexCap r.sub) :
    (inp.hexAccPrev + (1 : F circomPrime) * (inH inp.subPrev * (16 * inp.hexAccPrev
        + hexVal inp.byte) - inp.hexAccPrev)).val < 4096 := by
  have hkey : inp.hexAccPrev + (1 : F circomPrime) * (inH inp.subPrev * (16 * inp.hexAccPrev
        + hexVal inp.byte) - inp.hexAccPrev)
      = if (decide (r.sub = Sub.H1) || decide (r.sub = Sub.H2) || decide (r.sub = Sub.H3))
          then ((16 * r.hexAcc + Model.hexVal inp.byte.val : ℕ) : F circomPrime) else 0 := by
    rw [one_mul, inH_eq hE, hE.2.2.1, hexVal_eq]
    rcases hc : (decide (r.sub = Sub.H1) || decide (r.sub = Sub.H2) ||
        decide (r.sub = Sub.H3)) with _ | _ <;> simp [ind] <;> push_cast <;> ring
  rw [hkey]
  by_cases hc : (decide (r.sub = Sub.H1) || decide (r.sub = Sub.H2) ||
      decide (r.sub = Sub.H3)) = true
  · rw [if_pos hc]
    have hcap' : hexCap r.sub ≤ 256 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with (h | h) | h <;> rw [h] <;> decide
    have hlt : 16 * r.hexAcc + Model.hexVal inp.byte.val < 4096 := by
      have := hexVal_lt_16 inp.byte.val; omega
    have hp : (4096 : ℕ) < circomPrime := by decide
    rw [ZMod.val_natCast_of_lt (by omega)]
    exact hlt
  · rw [if_neg hc]; simp

lemma kIdxNext_val_lt (hE : EncodesPrev inp r) (hk : r.kIdx < kIdxMax) :
    (inp.kIdxPrev + (1 : F circomPrime) * (inp.stPrev[St.KEY] * (inp.kIdxPrev
        + emit inp.byte inp.stPrev inp.subPrev
          * (1 - (ohOf kIdxMax inp.kIdxPrev)[kIdxMax - 1])) - inp.kIdxPrev)).val
      < kIdxMax := by
  have hup := kIdx_update ((Model.signals r inp.byte.val r.st).emit) r.kIdx hk
  rw [one_mul, stPrev_get hE St.KEY, emit_eq hE r.st,
    kIdxOH_get hE hk (kIdxMax - 1) (by decide), hE.2.2.2.1]
  have hp : (kIdxMax : ℕ) < circomPrime := by decide
  by_cases hkey : r.st = St.KEY
  · rw [show ind (decide (r.st = St.KEY)) = 1 by simp [ind, hkey], one_mul]
    have key : (r.kIdx : F circomPrime) + ((r.kIdx : F circomPrime)
          + ind ((Model.signals r inp.byte.val r.st).emit)
            * (1 - ind (decide (kIdxMax - 1 = r.kIdx))) - (r.kIdx : F circomPrime))
        = ((min (r.kIdx + (if (Model.signals r inp.byte.val r.st).emit then 1 else 0))
            (kIdxMax - 1) : ℕ) : F circomPrime) := by linear_combination hup
    rw [key, ZMod.val_natCast_of_lt (by simp only [Model.kIdxMax] at hp ⊢; omega)]
    simp only [Model.kIdxMax]; omega
  · rw [show ind (decide (r.st = St.KEY)) = 0 by simp [ind, hkey], zero_mul]
    rw [show (r.kIdx : F circomPrime) + (0 - (r.kIdx : F circomPrime)) = 0 by ring]
    simp only [ZMod.val_zero, Model.kIdxMax]; omega

lemma ofsNext_val_lt (hE : EncodesPrev inp r) (ho : r.ofs < ofsMax)
    (hpv : r.st = St.PVAL → r.ofs = 0) :
    (inp.ofsPrev + (1 : F circomPrime) * (inVal inp.stPrev * inp.ofsPrev
        + vEmit inp.byte inp.stPrev inp.subPrev * (1 - (ohOf ofsMax inp.ofsPrev)[ofsMax - 1])
        - inp.ofsPrev)).val < ofsMax := by
  have hup := ofs_update ((Model.signals r inp.byte.val r.st).vEmit) r.ofs ho
  rw [one_mul, inVal_eq hE, vEmit_eq hE r.st, ofsOH_get hE ho (ofsMax - 1) (by decide),
    hE.2.2.2.2.2.2.1]
  have hp : (ofsMax : ℕ) < circomPrime := by decide
  by_cases hiv : inValP r.st = true
  · rw [show ind (inValP r.st) = 1 by simp [ind, hiv], one_mul]
    have key : (r.ofs : F circomPrime) + ((r.ofs : F circomPrime)
          + ind ((Model.signals r inp.byte.val r.st).vEmit)
            * (1 - ind (decide (ofsMax - 1 = r.ofs))) - (r.ofs : F circomPrime))
        = ((min (r.ofs + (if (Model.signals r inp.byte.val r.st).vEmit then 1 else 0))
            (ofsMax - 1) : ℕ) : F circomPrime) := by linear_combination hup
    rw [key, ZMod.val_natCast_of_lt (by simp only [Model.ofsMax] at hp ⊢; omega)]
    simp only [Model.ofsMax]; omega
  · simp only [Bool.not_eq_true] at hiv
    rw [show ind (inValP r.st) = 0 by simp [ind, hiv], zero_mul, zero_add]
    by_cases hv : (Model.signals r inp.byte.val r.st).vEmit = true
    · have hpval : r.st = St.PVAL :=
        vEmit_outside_value r.st hiv (vEmit_state r inp.byte.val r.st hv)
      have hofs0 : r.ofs = 0 := hpv hpval
      rw [show ind ((Model.signals r inp.byte.val r.st).vEmit) = 1 by simp [ind, hv],
        show ind (decide (ofsMax - 1 = r.ofs)) = 0 by simp [ind, hofs0]]
      rw [show (r.ofs : F circomPrime) + (1 * (1 - 0) - (r.ofs : F circomPrime))
        = 1 by ring]
      simp only [ZMod.val_one, Model.ofsMax]; omega
    · simp only [Bool.not_eq_true] at hv
      rw [show ind ((Model.signals r inp.byte.val r.st).vEmit) = 0 by simp [ind, hv]]
      rw [show (r.ofs : F circomPrime) + (0 * (1 - ind (decide (ofsMax - 1 = r.ofs)))
        - (r.ofs : F circomPrime)) = 0 by ring]
      simp only [ZMod.val_zero, Model.ofsMax]; omega

end Active

/-! ## The composition -/

set_option maxHeartbeats 1000000 in
/-- **The composition.**  The exact row identities of `Step.main`, plus the one
assumption a position needs about its byte, give the gadget's specification. -/
theorem spec_of_rows {inp : Inputs (F circomPrime)} {out : Outputs (F circomPrime)}
    (hb : inp.byte.val < 256) (hrow : RowSpec inp out) (d : ProverData (F circomPrime)) :
    Spec inp out d := by
  obtain ⟨hclB, hmB, hkU, hAccm, hsubB, hsubS, hsubRow, hstB, hstS, hstRow, hHex, hkidxlt,
    hKIdx, hMRow, hMatch, hClaim, hofslt, hOfs, hVEK, hMK, hTK, hNMem, hSel, hEx, hAsc⟩ := hrow
  refine ⟨hstB, hstS, hsubB, hsubS, ?_⟩
  intro r hw hE
  have hw' := hw
  obtain ⟨hhex, hkidxM, hofsM, hinv, hpval, hhexc⟩ := hw'
  have c6 : inp.claimPrev[6] = ind (decide (r.claim = some 6)) := claimPrev_get hE 6
  -- the per-position signals, which do not read the successor state
  have hOut : ∀ st' : St, OutSignals out r (Model.signals r inp.byte.val st') := by
    intro st'
    refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, ?_⟩
    · rw [hMatch k, matchOf_eq hE hkidxM st' k, ind_eq_ite]
    · rw [hVEK k, vEmit_eq hE st', claimPrev_get hE k, ind_and_prop]
    · rw [hMK k, minusFlag_eq hE st', claimPrev_get hE k, ind_and_prop]
    · rw [hTK, trueDone_eq hE st', c6, ind_and_prop]
  refine ⟨hAccm, ?_, ?_⟩
  · -- an inactive position freezes everything
    intro hact
    have hz : (1 : F circomPrime) - inp.accmNext = 0 := by rw [hact]; ring
    have hstN : ∀ j : Fin nSt, inp.stNext[j] = inp.stPrev[j] := fun j => by
      rw [hstRow j, hz]; ring
    have hsubN : ∀ j : Fin nSub, inp.subNext[j] = inp.subPrev[j] := fun j => by
      rw [hsubRow j, hz]; ring
    have hks : keyStart inp.stPrev inp.stNext = 0 := by
      simp only [keyStart, Fin.getElem_fin, hstN St.KEY, stPrev_get hE St.KEY, ind_mul_one_sub]
    refine ⟨⟨fun j => by rw [hstN j]; exact hE.1 j, fun j => by rw [hsubN j]; exact hE.2.1 j,
      ?_, ?_, fun k => ?_, fun k => ?_, ?_, ?_⟩, hOut r.st⟩
    · rw [hHex, hz, zero_mul, add_zero]; exact hE.2.2.1
    · rw [hKIdx, hz, zero_mul, add_zero]; exact hE.2.2.2.1
    · rw [hMRow k, hz, zero_mul, add_zero]; exact hE.2.2.2.2.1 k
    · rw [hClaim k, hz, zero_mul, add_zero]; exact hE.2.2.2.2.2.1 k
    · rw [hOfs, hz, zero_mul, add_zero]; exact hE.2.2.2.2.2.2.1
    · rw [hNMem, hks, add_zero]; exact hE.2.2.2.2.2.2.2
  · -- an active position takes the transition
    intro hact
    have ho : (1 : F circomPrime) - inp.accmNext = 1 := by rw [hact]; ring
    have hsubSpec : SubAutomaton.Spec
        { inStr := inStr inp.stPrev, active := 1 - inp.accmNext, cls := classesOf inp.byte.val,
          subPrev := inp.subPrev, subNext := inp.subNext } := ⟨hsubB, hsubS, hsubRow⟩
    have hsubN : ∀ j : Fin nSub, inp.subNext[j]
        = optInd (Model.stepSub (Model.inStr r.st) r.sub inp.byte.val) j :=
      fun j => AutomatonModel.subNext_of_active inp.byte.val hb r.sub (Model.inStr r.st) rfl
        (subPrev_ohOf hE) (inStr_eq hE) ho hsubSpec j
    have hmainSpec : MainAutomaton.Spec
        { active := 1 - inp.accmNext, closeQuote := closeQuote inp.byte inp.subPrev,
          cls := classesOf inp.byte.val, kinds := kinds inp.claimPrev, stPrev := inp.stPrev,
          stNext := inp.stNext } := ⟨hstB, hstS, hstRow⟩
    have hstN : ∀ j : Fin nSt, inp.stNext[j]
        = optInd (Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Sub.PLAIN)) r.st
            inp.byte.val) j :=
      fun j => AutomatonModel.stNext_of_active inp.byte.val hb r.st (Model.kindOf r.claim)
        (decide (r.sub = Sub.PLAIN)) rfl (closeQuote_eq hE) (kinds_eq hE) (stPrev_ohOf hE) ho
        hmainSpec j
    refine ⟨hstN, hsubN, ?_, ?_, ?_, ?_, ?_⟩
    · -- the successor accumulator still fits the next position's range check
      rw [hHex, ho]
      exact hexAccNext_val_lt hE hhexc
    · -- the successor key index still fits the next position's one-hot
      rw [hKIdx, ho]
      exact kIdxNext_val_lt hE hkidxM
    · -- the successor offset still fits the next position's one-hot
      rw [hOfs, ho]
      exact ofsNext_val_lt hE hofsM hpval
    · -- the two routing rows make a double transition a full step
      intro hsi hti
      obtain ⟨sub', hsub'⟩ := Option.isSome_iff_exists.mp hsi
      obtain ⟨st', hst'⟩ := Option.isSome_iff_exists.mp hti
      refine step_isSome_of hsub' hst' ?_ ?_
      · intro hwrite k hcl
        have h1 : write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 1 := by
          rw [write_eq hE st', hwrite]; rfl
        rw [h1, one_mul, sub_eq_zero, existsIn_some hE hofsM k hcl] at hEx
        exact of_decide_eq_true (ind_eq_one hEx)
      · intro hwrite hstr
        have h1 : write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 1 := by
          rw [write_eq hE st', hwrite]; rfl
        have h2 := stPrev_get hE St.STR
        rw [h1, h2, hstr] at hAsc
        simp only [decide_true, ByteClass.ind_true, one_mul, sub_eq_zero] at hAsc
        rw [ltAscii_eq hE hb hhex st'] at hAsc
        exact of_decide_eq_true (ind_eq_one hAsc.symm)
    · -- the successor registers and the routed cell
      intro r' hstep
      obtain ⟨hs1, hs2, hhx, hki, hcl, hof, hnm, hm⟩ := step_fields hstep
      have hENst : ∀ j : Fin nSt, inp.stNext[j] = if j = r'.st then 1 else 0 := by
        intro j
        rw [hstN j, hs2, optInd_some]
        rcases eq_or_ne r'.st j with h | h
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hh => h hh.symm)]
      have hENsub : ∀ j : Fin nSub, inp.subNext[j] = if j = r'.sub then 1 else 0 := by
        intro j
        rw [hsubN j, hs1, optInd_some]
        rcases eq_or_ne r'.sub j with h | h
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hh => h hh.symm)]
      have hkeyStart := keyStart_active hE hENst
      refine ⟨⟨hENst, hENsub, ?_, ?_, fun k => ?_, fun k => ?_, ?_, ?_⟩, hOut r'.st, ?_⟩
      · -- the `\uXXXX` accumulator
        rw [hHex, ho]
        exact hexAcc_active hE hstep
      · -- the key index
        rw [hKIdx, ho]
        exact kIdx_active hE hw hstep
      · -- the matcher registers
        rw [hMRow k, ho]
        exact m_active hb hE hw hstep hkeyStart k
      · -- the claim register
        rw [hClaim k, ho, hMatch k]
        exact claim_active hE hw hstep hkeyStart k
      · -- the value offset
        rw [hOfs, ho]
        exact ofs_active hE hw hstep
      · -- the member counter
        rw [hNMem]
        exact nMem_active hE hstep hkeyStart
      · -- the routed cell
        intro k hwrite hcl2
        have h1 : write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 1 := by
          rw [write_eq hE r'.st, hwrite]; rfl
        have hlt : r.ofs < Model.claimCap k := by
          rw [h1, one_mul, sub_eq_zero, existsIn_some hE hofsM k hcl2] at hEx
          exact of_decide_eq_true (ind_eq_one hEx)
        rw [h1, one_mul, sub_eq_zero, selected_eq hE hofsM k hcl2 hlt] at hSel
        rw [hSel, valOut_eq hE r'.st]

/-! ## The rows an honest prover has to produce

The mirror of `spec_of_rows`: from the honest-prover view of a position (the
`*Prev` half encodes `r`, the `*Next` half encodes the frozen `r` or the
model's successor) every row of `Step.main` holds. -/

lemma step_capOk {r r' : Regs} {b : ℕ} (h : Model.step r b = some r')
    (hwr : (Model.signals r b r'.st).write = true) (k : Claim) (hcl : r.claim = some k) :
    r.ofs < Model.claimCap k := by
  by_contra hlt
  obtain ⟨hsub, hst, -, -, -, -, -, -⟩ := step_fields h
  simp only [Model.step, Option.bind_eq_bind, hsub, hst, Option.bind] at h
  simp [hwr, hcl, hlt] at h

lemma step_asciiOk {r r' : Regs} {b : ℕ} (h : Model.step r b = some r')
    (hwr : (Model.signals r b r'.st).write = true) (hstr : r.st = St.STR) :
    (Model.signals r b r'.st).cp < 0x80 := by
  by_contra hlt
  obtain ⟨hsub, hst, -, -, -, -, -, -⟩ := step_fields h
  simp only [Model.step, Option.bind_eq_bind, hsub, hst, Option.bind] at h
  simp [hwr, hstr, hlt] at h

lemma sum_stPrev (hE : EncodesPrev inp r) : (∑ j : Fin nSt, inp.stPrev[j.val]) = 1 := by
  have h : ∀ j : Fin nSt, inp.stPrev[j.val] = if j = r.st then 1 else 0 := fun j => hE.1 j
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => h j)]
  simp

lemma sum_subPrev (hE : EncodesPrev inp r) : (∑ j : Fin nSub, inp.subPrev[j.val]) = 1 := by
  have h : ∀ j : Fin nSub, inp.subPrev[j.val] = if j = r.sub then 1 else 0 := fun j => hE.2.1 j
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => h j)]
  simp

lemma subMass_row (b : ℕ) (hb : b < 256) (s : Sub) (istr : Bool) (j : Fin nSub) :
    ind istr * SubAutomaton.massVal (classesOf b) (ohOf nSub ((s.val : ℕ) : F circomPrime)) j.val
        + (if j.val = 0 then 1 - ind istr else 0)
      = optInd (Model.stepSub istr s b) j := by
  cases istr with
  | true =>
      rw [ByteClass.ind_true, one_mul, AutomatonModel.massVal_eq b hb s j]
      simp
  | false =>
      rw [ByteClass.ind_false, zero_mul, zero_add,
        show Model.stepSub false s b = some Model.Sub.PLAIN from rfl, optInd_some]
      by_cases hj : (j : ℕ) = 0
      · rw [if_pos hj, if_pos (Fin.ext (n := nSub) hj.symm)]
        norm_num
      · rw [if_neg hj, if_neg (fun hh : Model.Sub.PLAIN = j => hj (by rw [← hh]; rfl))]

set_option maxHeartbeats 1000000 in
/-- **The honest prover's rows.**  Every row of `Step.main` holds at a position
whose `*Prev` half encodes `r` and whose `*Next` half is the frozen `r` (an
inactive position) or the model's successor (an active one). -/
theorem rows_of_encodes {inp : Inputs (F circomPrime)} {out : Outputs (F circomPrime)}
    (hb : inp.byte.val < 256) {r : Regs} (hw : WFRegs r) (hE : EncodesPrev inp r)
    (hacc : inp.accmNext = inp.accmPrev + inp.lenFlag)
    (hpa : (inp.accmNext = 1 ∧ EncodesNext inp r ∧
        (Model.signals r inp.byte.val r.st).write = false) ∨
      (inp.accmNext = 0 ∧ ∃ r', Model.step r inp.byte.val = some r' ∧ EncodesNext inp r' ∧
        WritesCell inp r (Model.signals r inp.byte.val r'.st)))
    (hMatch : ∀ k : Claim, out.match_[k]
      = matchOf k inp.byte inp.stPrev inp.subPrev inp.mPrev inp.kIdxPrev)
    (hVEK : ∀ k : Claim, out.vEmitK[k]
      = vEmit inp.byte inp.stPrev inp.subPrev * inp.claimPrev[k])
    (hMK : ∀ k : Claim, out.minusK[k] = minusFlag inp.byte inp.stPrev * inp.claimPrev[k])
    (hTK : out.trueK = trueDone inp.byte inp.stPrev * inp.claimPrev[6]) :
    RowSpec inp out := by
  have hkidxV : inp.kIdxPrev.val < kIdxMax := by
    have hp : r.kIdx < circomPrime := by
      have : (16 : ℕ) < circomPrime := by decide
      have := hw.2.1; simp only [Model.kIdxMax] at this; omega
    rw [hE.2.2.2.1, ZMod.val_natCast_of_lt hp]
    exact hw.2.1
  have hofsV : inp.ofsPrev.val < ofsMax := by
    have hp : r.ofs < circomPrime := by
      have : (129 : ℕ) < circomPrime := by decide
      have := hw.2.2.1; simp only [Model.ofsMax] at this; omega
    rw [hE.2.2.2.2.2.2.1, ZMod.val_natCast_of_lt hp]
    exact hw.2.2.1
  refine ⟨fun k => by rw [claimPrev_get hE k]; exact ind_isBool _,
    fun k => by rw [mPrev_get hE k]; exact ind_isBool _,
    by rw [kUnk_eq hE]; exact ind_isBool _, hacc,
    fun j => by rw [subPrev_get hE j]; exact ind_isBool _, sum_subPrev hE, ?_,
    fun j => by rw [stPrev_get hE j]; exact ind_isBool _, sum_stPrev hE, ?_,
    ?_, hkidxV, ?_, ?_, hMatch, ?_, hofsV, ?_, hVEK, hMK, hTK, ?_, ?_, ?_, ?_⟩
  all_goals rcases hpa with ⟨hact, hEN, hnw⟩ | ⟨hact, r', hstep, hEN, hwc⟩
  -- the sub automaton
  · intro j
    rw [hEN.2.1 j, hE.2.1 j, hact]
    ring
  · intro j
    rw [hEN.2.1 j, hact, sub_zero, one_mul, inStr_eq hE, subPrev_ohOf hE,
      subMass_row inp.byte.val hb r.sub (Model.inStr r.st) j, (step_fields hstep).1, optInd_some,
      ← subPrev_ohOf hE, hE.2.1 j]
    rcases eq_or_ne r'.sub j with h | h
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]; ring
  -- the main automaton
  · intro j
    rw [hEN.1 j, hE.1 j, hact]
    ring
  · intro j
    rw [hEN.1 j, hact, sub_zero, one_mul, closeQuote_eq hE, kinds_eq hE, stPrev_ohOf hE,
      AutomatonModel.mainMass_eq inp.byte.val hb r.st (Model.kindOf r.claim)
        (decide (r.sub = Sub.PLAIN)) _ rfl j, (step_fields hstep).2.1, optInd_some,
      ← stPrev_ohOf hE, hE.1 j]
    rcases eq_or_ne r'.st j with h | h
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]; ring
  -- the `\uXXXX` accumulator
  · rw [hEN.2.2.1, hE.2.2.1, hact]; ring
  · rw [hEN.2.2.1, hact, sub_zero]; exact (hexAcc_active hE hstep).symm
  -- the key index
  · rw [hEN.2.2.2.1, hE.2.2.2.1, hact]; ring
  · rw [hEN.2.2.2.1, hact, sub_zero]; exact (kIdx_active hE hw hstep).symm
  -- the matcher registers
  · intro k
    rw [hEN.2.2.2.2.1 k, hE.2.2.2.2.1 k, hact]
    ring
  · intro k
    have hks : keyStart inp.stPrev inp.stNext
        = ind ((Model.signals r inp.byte.val r'.st).keyStart) := keyStart_active hE hEN.1
    rw [hEN.2.2.2.2.1 k, hact, sub_zero]
    exact (m_active hb hE hw hstep hks k).symm
  -- the claim register
  · intro k
    rw [hEN.2.2.2.2.2.1 k, hE.2.2.2.2.2.1 k, hact, hMatch k]
    have hkc : matchOf k inp.byte inp.stPrev inp.subPrev inp.mPrev inp.kIdxPrev
        = ind ((Model.signals r inp.byte.val r.st).match_[k]) := matchOf_eq hE hw.2.1 r.st k
    ring
  · intro k
    have hks : keyStart inp.stPrev inp.stNext
        = ind ((Model.signals r inp.byte.val r'.st).keyStart) := keyStart_active hE hEN.1
    rw [hEN.2.2.2.2.2.1 k, hact, sub_zero, hMatch k]
    exact (claim_active hE hw hstep hks k).symm
  -- the value offset
  · rw [hEN.2.2.2.2.2.2.1, hE.2.2.2.2.2.2.1, hact]; ring
  · rw [hEN.2.2.2.2.2.2.1, hact, sub_zero]; exact (ofs_active hE hw hstep).symm
  -- the member counter
  · have hks : keyStart inp.stPrev inp.stNext = 0 := by
      rw [keyStart, hEN.1 St.KEY, hE.1 St.KEY]
      rcases eq_or_ne St.KEY r.st with h | h
      · rw [if_pos h]; ring
      · rw [if_neg h]; ring
    rw [hEN.2.2.2.2.2.2.2, hE.2.2.2.2.2.2.2, hks]
    ring
  · have hks : keyStart inp.stPrev inp.stNext
        = ind ((Model.signals r inp.byte.val r'.st).keyStart) := keyStart_active hE hEN.1
    rw [hEN.2.2.2.2.2.2.2]
    exact (nMem_active hE hstep hks).symm
  -- the routed value
  · rw [show write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 0 by
      rw [write_eq hE r.st, hnw]; rfl]
    ring
  · by_cases hwr : (Model.signals r inp.byte.val r'.st).write = true
    · obtain ⟨k, hcl⟩ : ∃ k : Claim, r.claim = some k := by
        rcases hc : r.claim with _ | k
        · exact absurd hwr (by simp [sig_write, hc, Model.kindOf])
        · exact ⟨k, rfl⟩
      have hlt := step_capOk hstep hwr k hcl
      rw [show write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 1 by
        rw [write_eq hE r'.st, hwr]; rfl, one_mul, sub_eq_zero,
        selected_eq hE hw.2.2.1 k hcl hlt, valOut_eq hE r'.st]
      exact hwc k hwr hcl
    · simp only [Bool.not_eq_true] at hwr
      rw [show write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 0 by
        rw [write_eq hE r'.st, hwr]; rfl]
      ring
  -- the cap
  · rw [show write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 0 by
      rw [write_eq hE r.st, hnw]; rfl]
    ring
  · by_cases hwr : (Model.signals r inp.byte.val r'.st).write = true
    · obtain ⟨k, hcl⟩ : ∃ k : Claim, r.claim = some k := by
        rcases hc : r.claim with _ | k
        · exact absurd hwr (by simp [sig_write, hc, Model.kindOf])
        · exact ⟨k, rfl⟩
      have hlt := step_capOk hstep hwr k hcl
      rw [show write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 1 by
        rw [write_eq hE r'.st, hwr]; rfl, one_mul, sub_eq_zero,
        existsIn_some hE hw.2.2.1 k hcl]
      simp [ind, hlt]
    · simp only [Bool.not_eq_true] at hwr
      rw [show write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 0 by
        rw [write_eq hE r'.st, hwr]; rfl]
      ring
  -- the ASCII check
  · rw [show write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 0 by
      rw [write_eq hE r.st, hnw]; rfl]
    ring
  · by_cases hstr : r.st = St.STR
    · by_cases hwr : (Model.signals r inp.byte.val r'.st).write = true
      · rw [show write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 1 by
          rw [write_eq hE r'.st, hwr]; rfl,
          show inp.stPrev[St.STR] = 1 by rw [stPrev_get hE St.STR, hstr]; rfl,
          one_mul, one_mul, ltAscii_eq hE hb hw.1 r'.st]
        simp [ind, step_asciiOk hstep hwr hstr]
      · simp only [Bool.not_eq_true] at hwr
        rw [show write inp.byte inp.stPrev inp.subPrev inp.claimPrev = 0 by
          rw [write_eq hE r'.st, hwr]; rfl]
        ring
    · rw [show inp.stPrev[St.STR] = 0 by rw [stPrev_get hE St.STR]; simp [hstr, ind]]
      ring

/-- The four per-position signals, as the circuit computes them from the
`*Prev` half. -/
def honestOut (inp : Inputs (F circomPrime)) : Outputs (F circomPrime) where
  match_ := Vector.ofFn fun k => matchOf k inp.byte inp.stPrev inp.subPrev inp.mPrev inp.kIdxPrev
  vEmitK := Vector.ofFn fun k => vEmit inp.byte inp.stPrev inp.subPrev * inp.claimPrev[k]
  minusK := Vector.ofFn fun k => minusFlag inp.byte inp.stPrev * inp.claimPrev[k]
  trueK := trueDone inp.byte inp.stPrev * inp.claimPrev[6]

@[simp] lemma honestOut_match (inp : Inputs (F circomPrime)) (k : Claim) :
    (honestOut inp).match_[k]
      = matchOf k inp.byte inp.stPrev inp.subPrev inp.mPrev inp.kIdxPrev := by
  simp [honestOut]

/-- `rows_of_encodes` at the signals the circuit itself computes. -/
theorem rows_of_encodes' {inp : Inputs (F circomPrime)}
    (hb : inp.byte.val < 256) {r : Regs} (hw : WFRegs r) (hE : EncodesPrev inp r)
    (hacc : inp.accmNext = inp.accmPrev + inp.lenFlag)
    (hpa : (inp.accmNext = 1 ∧ EncodesNext inp r ∧
        (Model.signals r inp.byte.val r.st).write = false) ∨
      (inp.accmNext = 0 ∧ ∃ r', Model.step r inp.byte.val = some r' ∧ EncodesNext inp r' ∧
        WritesCell inp r (Model.signals r inp.byte.val r'.st))) :
    RowSpec inp (honestOut inp) :=
  rows_of_encodes hb hw hE hacc hpa (fun k => by simp [honestOut])
    (fun k => by simp [honestOut]) (fun k => by simp [honestOut]) (by simp [honestOut])


end Step
end Solution.JSONExtract
