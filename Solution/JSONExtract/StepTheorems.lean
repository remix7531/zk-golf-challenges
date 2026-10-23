import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Mul
import Solution.JSONExtract.Model
import Solution.JSONExtract.ByteClass
import Solution.JSONExtract.OneHot
import Solution.JSONExtract.OneHotInterface
import Solution.JSONExtract.RouteSlot
import Solution.JSONExtract.SubAutomaton
import Solution.JSONExtract.MainAutomaton
import Solution.JSONExtract.Matcher
import Solution.JSONExtract.Interfaces

/-!
# Value-level twins of the per-position signals (`JSONExtract`)

`Step.lean` computes, from the byte and the registers before it, a chain of
witnessed products (`Mul`) before it constrains the witnessed registers after
the byte.  This file gives every one of those intermediate wires a *value*
level definition -- a plain field expression in the gadget's inputs -- so that
`Step.Assumptions` and `Step.Spec` can be stated over the inputs and outputs
alone, never over the gadget's internal variables.

It also collects the bundled interfaces (`Assumptions`, `Spec`,
`localLength`, `output`) of the gadgets `Step` calls, so the soundness and
completeness proofs never unfold a child's `main`, and the two arithmetic
facts those proofs need: the "at most one" consequence of a one-hot shaped
vector, and the bound `cp < 2 ^ 16` that `LessThan 16` demands.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Circomlib
open Model (nSt nSub nClaims kIdxMax ofsMax St Sub Claim)
open ByteClass (ind)

namespace Step

open Model.St Model.Sub

/-- A main-state vector at the value level. -/
abbrev StVec := Vector (F circomPrime) nSt
/-- A sub-state vector at the value level. -/
abbrev SubVec := Vector (F circomPrime) nSub
/-- A per-claim register at the value level. -/
abbrev ClVec := Vector (F circomPrime) nClaims

/-! ## The derived per-position signals -/

/-- The main automaton is inside a string. -/
def inStr (stPrev : StVec) : F circomPrime := stPrev[KEY] + stPrev[STR]

/-- A `"` closing a string: the sub-automaton must be in `PLAIN`. -/
def closeQuote (byte : F circomPrime) (subPrev : SubVec) : F circomPrime :=
  (classesOf byte.val).bytes.isQuote * subPrev[PLAIN]

/-- The claim register says a string claim is being read. -/
def kStr (claimPrev : ClVec) : F circomPrime :=
  claimPrev[0] + claimPrev[1] + claimPrev[2] + claimPrev[3] + claimPrev[4]
    + claimPrev[5] + claimPrev[7] + claimPrev[8]

/-- The claim register says an integer claim is being read. -/
def kInt (claimPrev : ClVec) : F circomPrime := claimPrev[9] + claimPrev[10]

/-- The claim register says the boolean claim is being read. -/
def kBool (claimPrev : ClVec) : F circomPrime := claimPrev[6]

/-- No known claim is being read. -/
def kUnk (claimPrev : ClVec) : F circomPrime :=
  1 - kStr claimPrev - kInt claimPrev - kBool claimPrev

/-- The four kind flags the main automaton's type gates read. -/
def kinds (claimPrev : ClVec) : Vector (F circomPrime) 4 :=
  #v[kStr claimPrev, kInt claimPrev, kBool claimPrev, kUnk claimPrev]

/-- An unescaped byte of a string emits itself. -/
def emitPlain (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) : F circomPrime :=
  inStr stPrev * subPrev[PLAIN] * (classesOf byte.val).classes.isUnescaped

/-- A simple escape emits its escape value. -/
def emitEsc (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) : F circomPrime :=
  inStr stPrev * subPrev[ESC] * (classesOf byte.val).classes.isSimpleEsc

/-- The last hex digit of a `\uXXXX` escape emits the decoded code point. -/
def emitU (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) : F circomPrime :=
  inStr stPrev * subPrev[H4] * (classesOf byte.val).classes.isHex

/-- The last continuation byte of a UTF-8 sequence emits the non-ASCII marker. -/
def emitUtf8 (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) : F circomPrime :=
  inStr stPrev * subPrev[C1] * (classesOf byte.val).classes.isCont

/-- A code point is emitted at this position. -/
def emit (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) : F circomPrime :=
  emitPlain byte stPrev subPrev + emitEsc byte stPrev subPrev + emitU byte stPrev subPrev
    + emitUtf8 byte stPrev subPrev

/-- The value of a hex digit (`0` off the hex classes). -/
def hexVal (byte : F circomPrime) : F circomPrime :=
  (classesOf byte.val).classes.isDigit * (byte - 0x30)
    + (classesOf byte.val).classes.isUpperHex * (byte - 0x37)
    + (classesOf byte.val).classes.isLowerHex * (byte - 0x57)

/-- The code point of a simple escape (`0` off the escape class). -/
def escVal (byte : F circomPrime) : F circomPrime :=
  0x22 * (classesOf byte.val).bytes.isQuote + 0x5C * (classesOf byte.val).bytes.isBackslash
    + 0x2F * (classesOf byte.val).bytes.isSlash + 0x08 * (classesOf byte.val).bytes.isLowerB
    + 0x0C * (classesOf byte.val).bytes.isLowerF + 0x0A * (classesOf byte.val).bytes.isLowerN
    + 0x0D * (classesOf byte.val).bytes.isLowerR + 0x09 * (classesOf byte.val).bytes.isLowerT

/-- The code point emitted at this position (`0` when nothing is emitted). -/
def cp (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) (hexAccPrev : F circomPrime) :
    F circomPrime :=
  emitPlain byte stPrev subPrev * byte + emitEsc byte stPrev subPrev * escVal byte
    + emitU byte stPrev subPrev * (16 * hexAccPrev + hexVal byte)
    + 0x80 * emitUtf8 byte stPrev subPrev

/-- The sub-automaton is reading the first three hex digits of a `\uXXXX`. -/
def inH (subPrev : SubVec) : F circomPrime := subPrev[H1] + subPrev[H2] + subPrev[H3]

/-- A key starts at this position. -/
def keyStart (stPrev stNext : StVec) : F circomPrime := stNext[KEY] * (1 - stPrev[KEY])

/-- A key closes at this position. -/
def keyClose (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) : F circomPrime :=
  stPrev[KEY] * closeQuote byte subPrev

/-- The key index at which claim `k`'s name is complete. -/
def kLen (k : Claim) : Fin kIdxMax := ⟨(Model.claimName k).length, Model.claimName_length_lt k⟩

/-- The byte matched claim `k`'s expected code point. -/
def eqCp (k : Claim) (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec)
    (hexAccPrev kIdxPrev : F circomPrime) : F circomPrime :=
  if cp byte stPrev subPrev hexAccPrev = Matcher.expected k (ohOf kIdxMax kIdxPrev) then 1 else 0

/-- The key closing at this position is claim `k`. -/
def matchOf (k : Claim) (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec)
    (mPrev : ClVec) (kIdxPrev : F circomPrime) : F circomPrime :=
  keyClose byte stPrev subPrev * (mPrev[k] * (ohOf kIdxMax kIdxPrev)[kLen k])

/-- The claim register is held (neither set nor reset) at this position. -/
def hold (byte : F circomPrime) (stPrev stNext : StVec) (subPrev : SubVec) : F circomPrime :=
  1 - keyClose byte stPrev subPrev - keyStart stPrev stNext

/-- A code point of a string value is emitted. -/
def strEmit (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) : F circomPrime :=
  emit byte stPrev subPrev * stPrev[STR]

/-- A decimal digit of an integer value is emitted. -/
def digitEmit (byte : F circomPrime) (stPrev : StVec) : F circomPrime :=
  (classesOf byte.val).classes.isDigit * (stPrev[PVAL] + stPrev[NSIGN] + stPrev[NINT])

/-- A value character is emitted at this position. -/
def vEmit (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) : F circomPrime :=
  strEmit byte stPrev subPrev + digitEmit byte stPrev

/-- The emitted character belongs to a known claim's value, so it is written. -/
def write (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) (claimPrev : ClVec) :
    F circomPrime :=
  vEmit byte stPrev subPrev * (kStr claimPrev + kInt claimPrev)

/-- The value written at this position. -/
def valOut (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec) (hexAccPrev : F circomPrime) :
    F circomPrime :=
  strEmit byte stPrev subPrev * cp byte stPrev subPrev hexAccPrev
    + digitEmit byte stPrev * (byte - 0x30)

/-- A value is being read (so the offset register is kept rather than cleared). -/
def inVal (stPrev : StVec) : F circomPrime :=
  1 - stPrev[PRE] - stPrev[OBJ] - stPrev[KEY] - stPrev[AKEY] - stPrev[PVAL]
    - stPrev[AVAL] - stPrev[SEP] - stPrev[END]

/-- A `-` is consumed in front of an integer value. -/
def minusFlag (byte : F circomPrime) (stPrev : StVec) : F circomPrime :=
  stPrev[PVAL] * (classesOf byte.val).bytes.isMinus

/-- `true` completes at this position. -/
def trueDone (byte : F circomPrime) (stPrev : StVec) : F circomPrime :=
  stPrev[T3] * (classesOf byte.val).bytes.isLowerE

/-! ## Routing -/

/-- The cell the claim register and the offset select, summed over the ten
string/integer slots. -/
def selected (claimPrev : ClVec) (ofsPrev : F circomPrime) (o : Output (F circomPrime)) :
    F circomPrime :=
  let oh := ohOf ofsMax ofsPrev
  claimPrev[0] * slotSel 32 (by decide) oh o.iss.bytes
    + claimPrev[1] * slotSel 32 (by decide) oh o.sub.bytes
    + claimPrev[2] * slotSel 128 (by decide) oh o.aud.bytes
    + claimPrev[3] * slotSel 128 (by decide) oh o.azp.bytes
    + claimPrev[4] * slotSel 64 (by decide) oh o.hd.bytes
    + claimPrev[5] * slotSel 128 (by decide) oh o.email.bytes
    + claimPrev[7] * slotSel 64 (by decide) oh o.nonce.bytes
    + claimPrev[8] * slotSel 64 (by decide) oh o.atHash.bytes
    + claimPrev[9] * slotSel 12 (by decide) oh o.iat.digits
    + claimPrev[10] * slotSel 12 (by decide) oh o.exp.digits

/-- The selected cell exists (the offset is within the selected slot's cap). -/
def existsIn (claimPrev : ClVec) (ofsPrev : F circomPrime) : F circomPrime :=
  let oh := ohOf ofsMax ofsPrev
  claimPrev[0] * slotEx 32 (by decide) oh + claimPrev[1] * slotEx 32 (by decide) oh
    + claimPrev[2] * slotEx 128 (by decide) oh + claimPrev[3] * slotEx 128 (by decide) oh
    + claimPrev[4] * slotEx 64 (by decide) oh + claimPrev[5] * slotEx 128 (by decide) oh
    + claimPrev[7] * slotEx 64 (by decide) oh + claimPrev[8] * slotEx 64 (by decide) oh
    + claimPrev[9] * slotEx 12 (by decide) oh + claimPrev[10] * slotEx 12 (by decide) oh

/-- The emitted code point is ASCII. -/
def ltAscii (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec)
    (hexAccPrev : F circomPrime) : F circomPrime :=
  if (cp byte stPrev subPrev hexAccPrev).val < 128 then 1 else 0

/-! ## Offset arithmetic

The three numeral identities the `Step` proofs need to normalise the witness
offsets the child gadgets sit at, so that the rows can be used as rewrite
rules without the elaborator reducing the offsets by `whnf`. -/

/-- The offset the sub-automaton block ends at. -/
lemma idxA : 23 + nSub * 2 = 49 := rfl

/-- The offset the main-automaton block ends at. -/
lemma idxB : 50 + (22 + nSt) = 99 := rfl

/-- A matcher's output sits seven cells into its block. -/
lemma idxC (a : ℕ) : a + 6 + 1 = a + 7 := by omega

/-! ## The arithmetic the `Step` proofs need -/

/-- A boolean vector summing to one is the indicator of a single index. -/
lemma exists_one_of_onehot {n : ℕ} (hn : n < circomPrime) (v : Vector (F circomPrime) n)
    (hb : ∀ i : Fin n, IsBool v[i.val]) (hs : (∑ i : Fin n, v[i.val]) = 1) :
    ∃ ℓ : Fin n, ∀ i : Fin n, v[i.val] = if i = ℓ then 1 else 0 := by
  have hv_bool : ∀ i : Fin n, (v[i.val]).val = 0 ∨ (v[i.val]).val = 1 :=
    fun i => LenFlags.isBool_val _ (hb i)
  have h_cast_sum : ((∑ i : Fin n, (v[i.val]).val : ℕ) : F circomPrime) = 1 := by
    rw [Nat.cast_sum, ← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hb i with h | h
    · rw [h]; simp
    · rw [h, ZMod.val_one, Nat.cast_one]
  have h_nat_sum : (∑ i : Fin n, (v[i.val]).val) = 1 :=
    OneHot.natSum_eq_one_of_cast hn (fun i => (v[i.val]).val) hv_bool h_cast_sum
  obtain ⟨ℓ, h1, h0⟩ :=
    LenFlags.exists_unique_of_sum_eq_one (fun i => (v[i.val]).val) hv_bool h_nat_sum
  refine ⟨ℓ, fun i => ?_⟩
  by_cases hi : i = ℓ
  · subst hi
    rcases hb i with h | h
    · rw [h, ZMod.val_zero] at h1; omega
    · simp [h]
  · rcases hb i with h | h
    · simp [hi, h]
    · exfalso; have := h0 i hi; rw [h, ZMod.val_one] at this; omega

/-- Multiplying by a boolean cannot increase the value. -/
lemma isBool_mul_val_le {a x : F circomPrime} (ha : IsBool a) : (a * x).val ≤ x.val := by
  rcases ha with h | h <;> simp [h]

/-- The escape value is one of the nine constants of the escape table. -/
lemma escVal_bound (byte : F circomPrime) :
    ∃ m : ℕ, m ≤ 92 ∧ escVal byte = (m : F circomPrime) := by
  simp only [escVal, classesOf, ind]
  by_cases h1 : byte.val = 0x22
  · exact ⟨0x22, by norm_num, by simp [h1]⟩
  by_cases h2 : byte.val = 0x5C
  · exact ⟨0x5C, by norm_num, by simp [h2]⟩
  by_cases h3 : byte.val = 0x2F
  · exact ⟨0x2F, by norm_num, by simp [h3]⟩
  by_cases h4 : byte.val = 0x62
  · exact ⟨0x08, by norm_num, by simp [h4]⟩
  by_cases h5 : byte.val = 0x66
  · exact ⟨0x0C, by norm_num, by simp [h5]⟩
  by_cases h6 : byte.val = 0x6E
  · exact ⟨0x0A, by norm_num, by simp [h6]⟩
  by_cases h7 : byte.val = 0x72
  · exact ⟨0x0D, by norm_num, by simp [h7]⟩
  by_cases h8 : byte.val = 0x74
  · exact ⟨0x09, by norm_num, by simp [h8]⟩
  exact ⟨0, by norm_num, by simp [h1, h2, h3, h4, h5, h6, h7, h8]⟩

/-- `ind` is boolean. -/
lemma ind_isBool (P : Bool) : IsBool (ind P) := by cases P <;> simp [ind, IsBool]

/-- The three hex classes are exclusive and pin the digit value. -/
lemma hex_classes (x : ℕ) :
    (Model.isDigit x = true ∧ Model.isUpperHex x = false ∧ Model.isLowerHex x = false
        ∧ 48 ≤ x ∧ x ≤ 57)
      ∨ (Model.isDigit x = false ∧ Model.isUpperHex x = true ∧ Model.isLowerHex x = false
        ∧ 65 ≤ x ∧ x ≤ 70)
      ∨ (Model.isDigit x = false ∧ Model.isUpperHex x = false ∧ Model.isLowerHex x = true
        ∧ 97 ≤ x ∧ x ≤ 102)
      ∨ (Model.isDigit x = false ∧ Model.isUpperHex x = false ∧ Model.isLowerHex x = false) := by
  simp only [Model.isDigit, Model.isUpperHex, Model.isLowerHex, Specs.JSON.digit0,
    Specs.JSON.digit9, Specs.JSON.upperA, Specs.JSON.upperF, Specs.JSON.lowerA,
    Specs.JSON.lowerF, Bool.and_eq_true, Bool.and_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not]
  omega

/-- The hex digit value is below 16. -/
lemma hexVal_bound (byte : F circomPrime) :
    ∃ m : ℕ, m ≤ 15 ∧ hexVal byte = (m : F circomPrime) := by
  have hb : ((byte.val : ℕ) : F circomPrime) = byte := by rw [ZMod.natCast_val, ZMod.cast_id]
  rcases hex_classes byte.val with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ |
    ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3⟩
  · refine ⟨byte.val - 48, by omega, ?_⟩
    have hc : ((byte.val - 48 : ℕ) : F circomPrime) = byte - 48 := by
      rw [Nat.cast_sub h4, hb]; norm_num
    rw [hc]
    simp [hexVal, classesOf, ind, h1, h2, h3]
  · refine ⟨byte.val - 55, by omega, ?_⟩
    have hc : ((byte.val - 55 : ℕ) : F circomPrime) = byte - 55 := by
      rw [Nat.cast_sub (by omega), hb]; norm_num
    rw [hc]
    simp [hexVal, classesOf, ind, h1, h2, h3]
  · refine ⟨byte.val - 87, by omega, ?_⟩
    have hc : ((byte.val - 87 : ℕ) : F circomPrime) = byte - 87 := by
      rw [Nat.cast_sub (by omega), hb]; norm_num
    rw [hc]
    simp [hexVal, classesOf, ind, h1, h2, h3]
  · exact ⟨0, by norm_num, by simp [hexVal, classesOf, ind, h1, h2, h3]⟩

/-- The `\uXXXX` accumulator plus the current digit is below `2 ^ 16`. -/
lemma hexAcc_bound (byte hexAccPrev : F circomPrime) (h : hexAccPrev.val < 4096) :
    (16 * hexAccPrev + hexVal byte).val < 2 ^ 16 := by
  obtain ⟨m, hm, hEq⟩ := hexVal_bound byte
  have hb : ((hexAccPrev.val : ℕ) : F circomPrime) = hexAccPrev := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have heq : 16 * hexAccPrev + hexVal byte
      = ((16 * hexAccPrev.val + m : ℕ) : F circomPrime) := by
    rw [hEq]
    push_cast
    rw [hb]
  have h65536 : (65536 : ℕ) < circomPrime := by decide
  have hlt : 16 * hexAccPrev.val + m < circomPrime := by omega
  rw [heq, ZMod.val_natCast_of_lt hlt]
  omega

/-- The emitted code point is below `2 ^ 16`, which is what `LessThan 16` demands.
The four emission flags are boolean and mutually exclusive (the sub-automaton
state is one-hot), so the code point is one of: a byte, an escape value, the
decoded `\uXXXX` value, or the non-ASCII marker. -/
lemma cp_val_lt (byte : F circomPrime) (stPrev : StVec) (subPrev : SubVec)
    (hexAccPrev : F circomPrime) (hbyte : byte.val < 256)
    (hstb : ∀ j : Fin nSt, IsBool stPrev[j.val]) (hsts : (∑ j : Fin nSt, stPrev[j.val]) = 1)
    (hsubb : ∀ j : Fin nSub, IsBool subPrev[j.val]) (hsubs : (∑ j : Fin nSub, subPrev[j.val]) = 1)
    (hhex : hexAccPrev.val < 4096) :
    (cp byte stPrev subPrev hexAccPrev).val < 2 ^ 16 := by
  obtain ⟨ℓs, hst⟩ := exists_one_of_onehot (by decide) stPrev hstb hsts
  obtain ⟨ℓ, hsub⟩ := exists_one_of_onehot (by decide) subPrev hsubb hsubs
  have hkey := hst St.KEY
  have hstr := hst St.STR
  have hinstr : IsBool (inStr stPrev) := by
    simp only [inStr, Fin.getElem_fin, hkey, hstr]
    rcases eq_or_ne St.KEY ℓs with h1 | h1
    · rcases eq_or_ne St.STR ℓs with h2 | h2
      · exact absurd (h1.trans h2.symm) (by decide)
      · rw [if_pos h1, if_neg h2, add_zero]; exact IsBool.one
    · rcases eq_or_ne St.STR ℓs with h2 | h2
      · rw [if_neg h1, if_pos h2, zero_add]; exact IsBool.one
      · rw [if_neg h1, if_neg h2, add_zero]; exact IsBool.zero
  have hPL := hsub Sub.PLAIN
  have hESC := hsub Sub.ESC
  have hH4 := hsub Sub.H4
  have hC1 := hsub Sub.C1
  have hEP : IsBool (emitPlain byte stPrev subPrev) :=
    IsBool.and_is_bool (IsBool.and_is_bool hinstr (hsubb Sub.PLAIN)) (ind_isBool _)
  have hEE : IsBool (emitEsc byte stPrev subPrev) :=
    IsBool.and_is_bool (IsBool.and_is_bool hinstr (hsubb Sub.ESC)) (ind_isBool _)
  have hEU : IsBool (emitU byte stPrev subPrev) :=
    IsBool.and_is_bool (IsBool.and_is_bool hinstr (hsubb Sub.H4)) (ind_isBool _)
  have hE8 : IsBool (emitUtf8 byte stPrev subPrev) :=
    IsBool.and_is_bool (IsBool.and_is_bool hinstr (hsubb Sub.C1)) (ind_isBool _)
  rcases eq_or_ne Sub.PLAIN ℓ with e | e0
  · rw [if_pos e] at hPL
    rw [if_neg (by rw [← e]; decide)] at hESC hH4 hC1
    have hcp : cp byte stPrev subPrev hexAccPrev = emitPlain byte stPrev subPrev * byte := by
      simp only [cp, emitEsc, emitU, emitUtf8, Fin.getElem_fin, hESC, hH4, hC1]
      ring
    rw [hcp]
    exact lt_of_le_of_lt (isBool_mul_val_le hEP) (by omega)
  rcases eq_or_ne Sub.ESC ℓ with e | e1
  · rw [if_pos e] at hESC
    rw [if_neg (by rw [← e]; decide)] at hPL hH4 hC1
    have hcp : cp byte stPrev subPrev hexAccPrev = emitEsc byte stPrev subPrev * escVal byte := by
      simp only [cp, emitPlain, emitU, emitUtf8, Fin.getElem_fin, hPL, hH4, hC1]
      ring
    obtain ⟨m, hm, hEq⟩ := escVal_bound byte
    have h93 : (93 : ℕ) < circomPrime := by decide
    have hval : (escVal byte).val = m := by
      rw [hEq, ZMod.val_natCast_of_lt (by omega)]
    rw [hcp]
    exact lt_of_le_of_lt (isBool_mul_val_le hEE) (by rw [hval]; omega)
  rcases eq_or_ne Sub.H4 ℓ with e | e2
  · rw [if_pos e] at hH4
    rw [if_neg (by rw [← e]; decide)] at hPL hESC hC1
    have hcp : cp byte stPrev subPrev hexAccPrev
        = emitU byte stPrev subPrev * (16 * hexAccPrev + hexVal byte) := by
      simp only [cp, emitPlain, emitEsc, emitUtf8, Fin.getElem_fin, hPL, hESC, hC1]
      ring
    rw [hcp]
    exact lt_of_le_of_lt (isBool_mul_val_le hEU) (hexAcc_bound byte hexAccPrev hhex)
  rcases eq_or_ne Sub.C1 ℓ with e | e3
  · rw [if_pos e] at hC1
    rw [if_neg (by rw [← e]; decide)] at hPL hESC hH4
    have hcp : cp byte stPrev subPrev hexAccPrev
        = emitUtf8 byte stPrev subPrev * (0x80 : F circomPrime) := by
      simp only [cp, emitPlain, emitEsc, emitU, Fin.getElem_fin, hPL, hESC, hH4]
      ring
    have h128 : ((0x80 : F circomPrime)).val = 128 := by
      have : (0x80 : F circomPrime) = ((128 : ℕ) : F circomPrime) := by norm_num
      rw [this, ZMod.val_natCast_of_lt (by decide)]
    rw [hcp]
    exact lt_of_le_of_lt (isBool_mul_val_le hE8) (by rw [h128]; omega)
  · rw [if_neg e0] at hPL
    rw [if_neg e1] at hESC
    rw [if_neg e2] at hH4
    rw [if_neg e3] at hC1
    have hcp : cp byte stPrev subPrev hexAccPrev = 0 := by
      simp only [cp, emitPlain, emitEsc, emitU, emitUtf8, Fin.getElem_fin, hPL, hESC, hH4, hC1]
      ring
    rw [hcp]
    simp


end Step
end Solution.JSONExtract
