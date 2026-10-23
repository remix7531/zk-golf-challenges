import Clean.Circomlib.Bitify
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Theorems
import Solution.JSONExtract.Model

/-!
# Helper lemmas for the `ByteClass` byte classifier

Three layers:

* `ind`, the `0/1` field indicator of a `Bool`, and the arithmetic that turns
  the circuit's products/sums of indicators back into indicators of `Bool`
  expressions;
* the interfaces of the two `circomlib` gadgets the classifier calls
  (`IsEqual`, `Num2Bits`), exposed without unfolding their implementations;
* the `Bool`-level mirrors of the bit polynomials the classifier computes,
  together with the `decide`-checked bridge to the `Model` predicates on the
  byte value.
-/

set_option maxRecDepth 8000

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Circomlib Utils.Bits

namespace ByteClass

/-! ## `ind` and its arithmetic -/

/-- `1` if the `Bool` holds, else `0`. -/
def ind (b : Bool) : F circomPrime := if b then 1 else 0

@[simp] lemma ind_true : ind true = 1 := rfl
@[simp] lemma ind_false : ind false = 0 := rfl

lemma ind_mul (P Q : Bool) : ind P * ind Q = ind (P && Q) := by
  cases P <;> cases Q <;> simp [ind]

lemma one_sub_ind (P : Bool) : 1 - ind P = ind (!P) := by cases P <;> simp [ind]

lemma ind_or (P Q : Bool) : ind P + ind Q - ind P * ind Q = ind (P || Q) := by
  cases P <;> cases Q <;> simp [ind]

lemma ind_add_disj {P Q : Bool} (h : (P && Q) = false) : ind P + ind Q = ind (P || Q) := by
  cases P <;> cases Q <;> simp_all [ind]

lemma ind_sub {P Q : Bool} (h : (Q && !P) = false) : ind P - ind Q = ind (P && !Q) := by
  cases P <;> cases Q <;> simp_all [ind]


lemma one_add_neg_ind (P : Bool) : 1 + -ind P = ind (!P) := by cases P <;> simp [ind]

lemma ind_add_not (P Q : Bool) : ind (!P) + ind (P && Q) = ind (!P || Q) := by
  cases P <;> cases Q <;> simp [ind]

lemma ind_add_sub_and (P Q : Bool) : ind P + ind Q + -ind (P && Q) = ind (P || Q) := by
  cases P <;> cases Q <;> simp [ind]

lemma ind_add_neg {P Q : Bool} (h : (Q && !P) = false) : ind P + -ind Q = ind (P && !Q) := by
  cases P <;> cases Q <;> simp_all [ind]

lemma ind_add_neg2 {P Q R : Bool} (hQ : (Q && !P) = false) (hR : (R && !P) = false)
    (hQR : (Q && R) = false) : ind P + -ind Q + -ind R = ind (P && !Q && !R) := by
  cases P <;> cases Q <;> cases R <;> simp_all [ind]

lemma or_disj {P Q R : Bool} (h1 : (P && R) = false) (h2 : (Q && R) = false) :
    ((P || Q) && R) = false := by cases P <;> cases Q <;> cases R <;> simp_all

lemma beq_disj (b c d : ℕ) (h : c ≠ d) : ((b == c) && (b == d)) = false := by
  by_cases hb : b = c
  · subst hb; simp [h]
  · rw [show (b == c) = false from beq_eq_false_iff_ne.mpr hb, Bool.false_and]

/-! ## Gadget interfaces -/

/-- Every byte constant the classifier tests against is below the modulus. -/
lemma lt_circomPrime {c : ℕ} (hc : c < 256) : c < circomPrime := by
  have := factCircomGt2_33.out
  have : (256 : ℕ) < 2 ^ 33 := by norm_num
  omega

lemma eq_iff_val (x : F circomPrime) {c : ℕ} (hc : c < circomPrime) :
    x = ((c : ℕ) : F circomPrime) ↔ x.val = c := by
  constructor
  · intro h; rw [h, ZMod.val_natCast_of_lt hc]
  · intro h; rw [← h, ZMod.natCast_val, ZMod.cast_id]

/-- An `IsEqual` flag against a small constant is the indicator of the byte
value being that constant. -/
lemma isEqual_ind (x : F circomPrime) (c : ℕ) (y : F circomPrime)
    (hy : y = ((c : ℕ) : F circomPrime)) (hc : c < 256) :
    (if x = y then (1 : F circomPrime) else 0) = ind (x.val == c) := by
  subst hy
  by_cases hx : x.val = c
  · rw [if_pos ((eq_iff_val x (lt_circomPrime hc)).mpr hx)]
    simp [ind, hx]
  · rw [if_neg (fun hh => hx ((eq_iff_val x (lt_circomPrime hc)).mp hh))]
    simp [ind, hx]


/-! ### The classifier's equality flags, one lemma per tested byte -/

lemma ind_eq_123 (x : F circomPrime) :
    (if x = (123 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 123) :=
  isEqual_ind x 123 123 (by norm_num) (by norm_num)

lemma ind_eq_125 (x : F circomPrime) :
    (if x = (125 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 125) :=
  isEqual_ind x 125 125 (by norm_num) (by norm_num)

lemma ind_eq_34 (x : F circomPrime) :
    (if x = (34 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 34) :=
  isEqual_ind x 34 34 (by norm_num) (by norm_num)

lemma ind_eq_58 (x : F circomPrime) :
    (if x = (58 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 58) :=
  isEqual_ind x 58 58 (by norm_num) (by norm_num)

lemma ind_eq_44 (x : F circomPrime) :
    (if x = (44 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 44) :=
  isEqual_ind x 44 44 (by norm_num) (by norm_num)

lemma ind_eq_45 (x : F circomPrime) :
    (if x = (45 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 45) :=
  isEqual_ind x 45 45 (by norm_num) (by norm_num)

lemma ind_eq_43 (x : F circomPrime) :
    (if x = (43 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 43) :=
  isEqual_ind x 43 43 (by norm_num) (by norm_num)

lemma ind_eq_46 (x : F circomPrime) :
    (if x = (46 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 46) :=
  isEqual_ind x 46 46 (by norm_num) (by norm_num)

lemma ind_eq_92 (x : F circomPrime) :
    (if x = (92 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 92) :=
  isEqual_ind x 92 92 (by norm_num) (by norm_num)

lemma ind_eq_47 (x : F circomPrime) :
    (if x = (47 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 47) :=
  isEqual_ind x 47 47 (by norm_num) (by norm_num)

lemma ind_eq_101 (x : F circomPrime) :
    (if x = (101 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 101) :=
  isEqual_ind x 101 101 (by norm_num) (by norm_num)

lemma ind_eq_69 (x : F circomPrime) :
    (if x = (69 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 69) :=
  isEqual_ind x 69 69 (by norm_num) (by norm_num)

lemma ind_eq_98 (x : F circomPrime) :
    (if x = (98 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 98) :=
  isEqual_ind x 98 98 (by norm_num) (by norm_num)

lemma ind_eq_102 (x : F circomPrime) :
    (if x = (102 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 102) :=
  isEqual_ind x 102 102 (by norm_num) (by norm_num)

lemma ind_eq_110 (x : F circomPrime) :
    (if x = (110 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 110) :=
  isEqual_ind x 110 110 (by norm_num) (by norm_num)

lemma ind_eq_114 (x : F circomPrime) :
    (if x = (114 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 114) :=
  isEqual_ind x 114 114 (by norm_num) (by norm_num)

lemma ind_eq_116 (x : F circomPrime) :
    (if x = (116 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 116) :=
  isEqual_ind x 116 116 (by norm_num) (by norm_num)

lemma ind_eq_117 (x : F circomPrime) :
    (if x = (117 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 117) :=
  isEqual_ind x 117 117 (by norm_num) (by norm_num)

lemma ind_eq_97 (x : F circomPrime) :
    (if x = (97 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 97) :=
  isEqual_ind x 97 97 (by norm_num) (by norm_num)

lemma ind_eq_108 (x : F circomPrime) :
    (if x = (108 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 108) :=
  isEqual_ind x 108 108 (by norm_num) (by norm_num)

lemma ind_eq_115 (x : F circomPrime) :
    (if x = (115 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 115) :=
  isEqual_ind x 115 115 (by norm_num) (by norm_num)

lemma ind_eq_48 (x : F circomPrime) :
    (if x = (48 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 48) :=
  isEqual_ind x 48 48 (by norm_num) (by norm_num)

lemma ind_eq_224 (x : F circomPrime) :
    (if x = (224 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 224) :=
  isEqual_ind x 224 224 (by norm_num) (by norm_num)

lemma ind_eq_237 (x : F circomPrime) :
    (if x = (237 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 237) :=
  isEqual_ind x 237 237 (by norm_num) (by norm_num)

lemma ind_eq_240 (x : F circomPrime) :
    (if x = (240 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 240) :=
  isEqual_ind x 240 240 (by norm_num) (by norm_num)

lemma ind_eq_244 (x : F circomPrime) :
    (if x = (244 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 244) :=
  isEqual_ind x 244 244 (by norm_num) (by norm_num)

lemma ind_eq_9 (x : F circomPrime) :
    (if x = (9 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 9) :=
  isEqual_ind x 9 9 (by norm_num) (by norm_num)

lemma ind_eq_10 (x : F circomPrime) :
    (if x = (10 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 10) :=
  isEqual_ind x 10 10 (by norm_num) (by norm_num)

lemma ind_eq_13 (x : F circomPrime) :
    (if x = (13 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 13) :=
  isEqual_ind x 13 13 (by norm_num) (by norm_num)

lemma ind_eq_32 (x : F circomPrime) :
    (if x = (32 : F circomPrime) then (1 : F circomPrime) else 0) = ind (x.val == 32) :=
  isEqual_ind x 32 32 (by norm_num) (by norm_num)

@[simp] lemma num2Bits_Assumptions (x : F circomPrime) (hn : 2 ^ 8 < circomPrime)
    (d : ProverData (F circomPrime)) :
    (Num2Bits.circuit 8 hn).Assumptions x d = True := rfl

@[simp] lemma num2Bits_Spec (x : F circomPrime) (hn : 2 ^ 8 < circomPrime)
    (o : Vector (F circomPrime) 8) (d : ProverData (F circomPrime)) :
    (Num2Bits.circuit 8 hn).Spec x o d = (x.val < 2 ^ 8 ∧ o = fieldToBits 8 x) := rfl

@[simp] lemma num2Bits_ProverAssumptions (x : F circomPrime) (hn : 2 ^ 8 < circomPrime)
    (d : ProverData (F circomPrime)) (h : ProverHint (F circomPrime)) :
    (Num2Bits.circuit 8 hn).ProverAssumptions x d h = (x.val < 2 ^ 8) := rfl

@[simp] lemma num2Bits_channelsWithRequirements (hn : 2 ^ 8 < circomPrime) :
    (Num2Bits.circuit 8 hn).channelsWithRequirements = [] := rfl

@[simp] lemma num2Bits_localLength (x : Var field (F circomPrime)) (hn : 2 ^ 8 < circomPrime) :
    (Num2Bits.circuit 8 hn).localLength x = 8 := rfl

@[simp] lemma num2Bits_output (x : Var field (F circomPrime)) (hn : 2 ^ 8 < circomPrime) (k : ℕ) :
    (Num2Bits.circuit 8 hn).output x k = varFromOffset (fields 8) k := rfl

/-- The bits `Num2Bits` returns are the indicators of the byte's bits. -/
lemma fieldToBits_ind (x : F circomPrime) (i : ℕ) (hi : i < 8) :
    (fieldToBits 8 x)[i]'(by simpa using hi) = ind (x.val.testBit i) := by
  simp only [fieldToBits, toBits, Vector.getElem_map, Vector.getElem_mapRange, ind]
  split <;> simp


/-! ### `Bool`-level bridges, checked by `decide` over all 256 bytes -/

lemma bridge_digit : ∀ i : Fin 256,
    (!i.val.testBit 7 && !i.val.testBit 6 && i.val.testBit 5 && i.val.testBit 4 && (!i.val.testBit 3 || !i.val.testBit 2 && !i.val.testBit 1)) = Model.isDigit i.val := by decide

lemma digit_ind (b : ℕ) (hb : b < 256) :
    (1 + -ind (b.testBit 7)) * (1 + -ind (b.testBit 6)) * ind (b.testBit 5) * ind (b.testBit 4) * (1 + -ind (b.testBit 3) + ind (b.testBit 3) * ((1 + -ind (b.testBit 2)) * (1 + -ind (b.testBit 1)))) = ind (Model.isDigit b) := by
  simp only [one_add_neg_ind, ind_mul, ind_add_not, ind_add_sub_and]
  exact congrArg ind (bridge_digit ⟨b, hb⟩)

lemma bridge_unescaped : ∀ i : Fin 256,
    (!i.val.testBit 7 && (i.val.testBit 6 || i.val.testBit 5) && !(i.val == 34) && !(i.val == 92)) = Model.isUnescaped i.val := by decide

lemma unescaped_ind (b : ℕ) (hb : b < 256) :
    (1 + -ind (b.testBit 7)) * (ind (b.testBit 6) + ind (b.testBit 5) + -(ind (b.testBit 6) * ind (b.testBit 5))) * (1 + -ind (b == 34)) * (1 + -ind (b == 92)) = ind (Model.isUnescaped b) := by
  simp only [one_add_neg_ind, ind_mul, ind_add_not, ind_add_sub_and]
  exact congrArg ind (bridge_unescaped ⟨b, hb⟩)

lemma bridge_cont : ∀ i : Fin 256,
    (i.val.testBit 7 && !i.val.testBit 6) = Model.isCont i.val := by decide

lemma cont_ind (b : ℕ) (hb : b < 256) :
    ind (b.testBit 7) * (1 + -ind (b.testBit 6)) = ind (Model.isCont b) := by
  simp only [one_add_neg_ind, ind_mul, ind_add_not, ind_add_sub_and]
  exact congrArg ind (bridge_cont ⟨b, hb⟩)

lemma bridge_contA0BF : ∀ i : Fin 256,
    (i.val.testBit 7 && !i.val.testBit 6 && i.val.testBit 5) = Model.isContA0BF i.val := by decide

lemma contA0BF_ind (b : ℕ) (hb : b < 256) :
    ind (b.testBit 7) * (1 + -ind (b.testBit 6)) * ind (b.testBit 5) = ind (Model.isContA0BF b) := by
  simp only [one_add_neg_ind, ind_mul, ind_add_not, ind_add_sub_and]
  exact congrArg ind (bridge_contA0BF ⟨b, hb⟩)

lemma bridge_cont809F : ∀ i : Fin 256,
    (i.val.testBit 7 && !i.val.testBit 6 && !i.val.testBit 5) = Model.isCont809F i.val := by decide

lemma cont809F_ind (b : ℕ) (hb : b < 256) :
    ind (b.testBit 7) * (1 + -ind (b.testBit 6)) * (1 + -ind (b.testBit 5)) = ind (Model.isCont809F b) := by
  simp only [one_add_neg_ind, ind_mul, ind_add_not, ind_add_sub_and]
  exact congrArg ind (bridge_cont809F ⟨b, hb⟩)

lemma bridge_cont90BF : ∀ i : Fin 256,
    (i.val.testBit 7 && !i.val.testBit 6 && (i.val.testBit 5 || i.val.testBit 4)) = Model.isCont90BF i.val := by decide

lemma cont90BF_ind (b : ℕ) (hb : b < 256) :
    ind (b.testBit 7) * (1 + -ind (b.testBit 6)) * (ind (b.testBit 5) + ind (b.testBit 4) + -(ind (b.testBit 5) * ind (b.testBit 4))) = ind (Model.isCont90BF b) := by
  simp only [one_add_neg_ind, ind_mul, ind_add_not, ind_add_sub_and]
  exact congrArg ind (bridge_cont90BF ⟨b, hb⟩)

lemma bridge_cont808F : ∀ i : Fin 256,
    (i.val.testBit 7 && !i.val.testBit 6 && !i.val.testBit 5 && !i.val.testBit 4) = Model.isCont808F i.val := by decide

lemma cont808F_ind (b : ℕ) (hb : b < 256) :
    ind (b.testBit 7) * (1 + -ind (b.testBit 6)) * (1 + -ind (b.testBit 5)) * (1 + -ind (b.testBit 4)) = ind (Model.isCont808F b) := by
  simp only [one_add_neg_ind, ind_mul, ind_add_not, ind_add_sub_and]
  exact congrArg ind (bridge_cont808F ⟨b, hb⟩)


/-! ### Sums of equality flags -/

lemma bridge_ws : ∀ i : Fin 256, ((((i.val == 9) || (i.val == 10)) || (i.val == 13)) || (i.val == 32)) = Model.isWs i.val := by decide

lemma ws_ind (b : ℕ) (hb : b < 256) :
    ind (b == 9) + ind (b == 10) + ind (b == 13) + ind (b == 32) = ind (Model.isWs b) := by
  have e1 : ind (b == 9) + ind (b == 10) = ind ((b == 9) || (b == 10)) :=
    ind_add_disj (by by_cases h : b = 10 <;> simp [h])
  have e2 : ind ((b == 9) || (b == 10)) + ind (b == 13) = ind (((b == 9) || (b == 10)) || (b == 13)) :=
    ind_add_disj (by by_cases h : b = 13 <;> simp [h])
  have e3 : ind (((b == 9) || (b == 10)) || (b == 13)) + ind (b == 32) = ind ((((b == 9) || (b == 10)) || (b == 13)) || (b == 32)) :=
    ind_add_disj (by by_cases h : b = 32 <;> simp [h])
  rw [e1, e2, e3]
  exact congrArg ind (bridge_ws ⟨b, hb⟩)

lemma bridge_simpleEsc : ∀ i : Fin 256, ((((((((i.val == 34) || (i.val == 92)) || (i.val == 47)) || (i.val == 98)) || (i.val == 102)) || (i.val == 110)) || (i.val == 114)) || (i.val == 116)) = Model.isSimpleEsc i.val := by decide

lemma simpleEsc_ind (b : ℕ) (hb : b < 256) :
    ind (b == 34) + ind (b == 92) + ind (b == 47) + ind (b == 98) + ind (b == 102) + ind (b == 110) + ind (b == 114) + ind (b == 116) = ind (Model.isSimpleEsc b) := by
  have e1 : ind (b == 34) + ind (b == 92) = ind ((b == 34) || (b == 92)) :=
    ind_add_disj (by by_cases h : b = 92 <;> simp [h])
  have e2 : ind ((b == 34) || (b == 92)) + ind (b == 47) = ind (((b == 34) || (b == 92)) || (b == 47)) :=
    ind_add_disj (by by_cases h : b = 47 <;> simp [h])
  have e3 : ind (((b == 34) || (b == 92)) || (b == 47)) + ind (b == 98) = ind ((((b == 34) || (b == 92)) || (b == 47)) || (b == 98)) :=
    ind_add_disj (by by_cases h : b = 98 <;> simp [h])
  have e4 : ind ((((b == 34) || (b == 92)) || (b == 47)) || (b == 98)) + ind (b == 102) = ind (((((b == 34) || (b == 92)) || (b == 47)) || (b == 98)) || (b == 102)) :=
    ind_add_disj (by by_cases h : b = 102 <;> simp [h])
  have e5 : ind (((((b == 34) || (b == 92)) || (b == 47)) || (b == 98)) || (b == 102)) + ind (b == 110) = ind ((((((b == 34) || (b == 92)) || (b == 47)) || (b == 98)) || (b == 102)) || (b == 110)) :=
    ind_add_disj (by by_cases h : b = 110 <;> simp [h])
  have e6 : ind ((((((b == 34) || (b == 92)) || (b == 47)) || (b == 98)) || (b == 102)) || (b == 110)) + ind (b == 114) = ind (((((((b == 34) || (b == 92)) || (b == 47)) || (b == 98)) || (b == 102)) || (b == 110)) || (b == 114)) :=
    ind_add_disj (by by_cases h : b = 114 <;> simp [h])
  have e7 : ind (((((((b == 34) || (b == 92)) || (b == 47)) || (b == 98)) || (b == 102)) || (b == 110)) || (b == 114)) + ind (b == 116) = ind ((((((((b == 34) || (b == 92)) || (b == 47)) || (b == 98)) || (b == 102)) || (b == 110)) || (b == 114)) || (b == 116)) :=
    ind_add_disj (by by_cases h : b = 116 <;> simp [h])
  rw [e1, e2, e3, e4, e5, e6, e7]
  exact congrArg ind (bridge_simpleEsc ⟨b, hb⟩)

lemma bridge_expLetter : ∀ i : Fin 256, ((i.val == 101) || (i.val == 69)) = Model.isExpLetter i.val := by decide

lemma expLetter_ind (b : ℕ) (hb : b < 256) :
    ind (b == 101) + ind (b == 69) = ind (Model.isExpLetter b) := by
  have e1 : ind (b == 101) + ind (b == 69) = ind ((b == 101) || (b == 69)) :=
    ind_add_disj (by by_cases h : b = 69 <;> simp [h])
  rw [e1]
  exact congrArg ind (bridge_expLetter ⟨b, hb⟩)

lemma bridge_sign : ∀ i : Fin 256, ((i.val == 43) || (i.val == 45)) = Model.isSign i.val := by decide

lemma sign_ind (b : ℕ) (hb : b < 256) :
    ind (b == 43) + ind (b == 45) = ind (Model.isSign b) := by
  have e1 : ind (b == 43) + ind (b == 45) = ind ((b == 43) || (b == 45)) :=
    ind_add_disj (by by_cases h : b = 45 <;> simp [h])
  rw [e1]
  exact congrArg ind (bridge_sign ⟨b, hb⟩)


/-! ### Flags built by subtracting equality flags -/

lemma bridge_digitNz_disj : ∀ i : Fin 256, ((i.val == 48) && !Model.isDigit i.val) = false := by decide

lemma bridge_digitNz : ∀ i : Fin 256,
    (Model.isDigit i.val && !(i.val == 48)) = Model.isDigitNz i.val := by decide

lemma digitNz_ind (b : ℕ) (hb : b < 256) :
    (1 + -ind (b.testBit 7)) * (1 + -ind (b.testBit 6)) * ind (b.testBit 5) * ind (b.testBit 4) * (1 + -ind (b.testBit 3) + ind (b.testBit 3) * ((1 + -ind (b.testBit 2)) * (1 + -ind (b.testBit 1)))) + -ind (b == 48) = ind (Model.isDigitNz b) := by
  rw [digit_ind b hb, ind_add_neg (bridge_digitNz_disj ⟨b, hb⟩)]
  exact congrArg ind (bridge_digitNz ⟨b, hb⟩)

lemma bridge_lead3_disjE0 : ∀ i : Fin 256,
    ((i.val == 224) &&
      !(i.val.testBit 7 && i.val.testBit 6 && i.val.testBit 5 && !i.val.testBit 4)) = false := by decide

lemma bridge_lead3_disjED : ∀ i : Fin 256,
    ((i.val == 237) &&
      !(i.val.testBit 7 && i.val.testBit 6 && i.val.testBit 5 && !i.val.testBit 4)) = false := by decide

lemma bridge_lead3 : ∀ i : Fin 256,
    (i.val.testBit 7 && i.val.testBit 6 && i.val.testBit 5 && !i.val.testBit 4 &&
      !(i.val == 224) && !(i.val == 237)) = Model.isLead3 i.val := by decide

lemma lead3_ind (b : ℕ) (hb : b < 256) :
    ind (b.testBit 7) * ind (b.testBit 6) * ind (b.testBit 5) * (1 + -ind (b.testBit 4)) + -ind (b == 224) + -ind (b == 237) =
      ind (Model.isLead3 b) := by
  simp only [one_add_neg_ind, ind_mul]
  rw [ind_add_neg2 (bridge_lead3_disjE0 ⟨b, hb⟩) (bridge_lead3_disjED ⟨b, hb⟩)
    (beq_disj b 224 237 (by norm_num))]
  exact congrArg ind (bridge_lead3 ⟨b, hb⟩)


/-! ### The hex classes and the two corrected lead bytes

`isUpperHex`/`isLowerHex` are a high-nibble prefix times the low-nibble test
`1 ≤ low ≤ 6`, `isHex` is the disjoint sum of the three hex families, `isLead2`
excludes the two overlong lead bytes `0xC0`/`0xC1` (bits `4..1` all clear), and
`isLead4` is `1111 00xx` minus `0xF0`. -/

lemma bridge_upperHex : ∀ i : Fin 256,
    (!i.val.testBit 7 && i.val.testBit 6 && !i.val.testBit 5 && !i.val.testBit 4 &&
      (!i.val.testBit 3 && (i.val.testBit 2 || i.val.testBit 1 || i.val.testBit 0) &&
        !(i.val.testBit 2 && i.val.testBit 1 && i.val.testBit 0))) = Model.isUpperHex i.val := by decide

lemma bridge_lowerHex : ∀ i : Fin 256,
    (!i.val.testBit 7 && i.val.testBit 6 && i.val.testBit 5 && !i.val.testBit 4 &&
      (!i.val.testBit 3 && (i.val.testBit 2 || i.val.testBit 1 || i.val.testBit 0) &&
        !(i.val.testBit 2 && i.val.testBit 1 && i.val.testBit 0))) = Model.isLowerHex i.val := by decide

/-- The digit and upper-hex families are disjoint. -/
lemma bridge_hex_disjDU : ∀ i : Fin 256,
    ((!i.val.testBit 7 && !i.val.testBit 6 && i.val.testBit 5 && i.val.testBit 4 &&
        (!i.val.testBit 3 || !i.val.testBit 2 && !i.val.testBit 1)) &&
      (!i.val.testBit 7 && i.val.testBit 6 && !i.val.testBit 5 && !i.val.testBit 4 &&
        (!i.val.testBit 3 && (i.val.testBit 2 || i.val.testBit 1 || i.val.testBit 0) &&
          !(i.val.testBit 2 && i.val.testBit 1 && i.val.testBit 0)))) = false := by decide

/-- The lower-hex family is disjoint from the other two. -/
lemma bridge_hex_disjL : ∀ i : Fin 256,
    (((!i.val.testBit 7 && !i.val.testBit 6 && i.val.testBit 5 && i.val.testBit 4 &&
          (!i.val.testBit 3 || !i.val.testBit 2 && !i.val.testBit 1)) ||
        (!i.val.testBit 7 && i.val.testBit 6 && !i.val.testBit 5 && !i.val.testBit 4 &&
          (!i.val.testBit 3 && (i.val.testBit 2 || i.val.testBit 1 || i.val.testBit 0) &&
            !(i.val.testBit 2 && i.val.testBit 1 && i.val.testBit 0)))) &&
      (!i.val.testBit 7 && i.val.testBit 6 && i.val.testBit 5 && !i.val.testBit 4 &&
        (!i.val.testBit 3 && (i.val.testBit 2 || i.val.testBit 1 || i.val.testBit 0) &&
          !(i.val.testBit 2 && i.val.testBit 1 && i.val.testBit 0)))) = false := by decide

lemma bridge_hex : ∀ i : Fin 256,
    (((!i.val.testBit 7 && !i.val.testBit 6 && i.val.testBit 5 && i.val.testBit 4 &&
          (!i.val.testBit 3 || !i.val.testBit 2 && !i.val.testBit 1)) ||
        (!i.val.testBit 7 && i.val.testBit 6 && !i.val.testBit 5 && !i.val.testBit 4 &&
          (!i.val.testBit 3 && (i.val.testBit 2 || i.val.testBit 1 || i.val.testBit 0) &&
            !(i.val.testBit 2 && i.val.testBit 1 && i.val.testBit 0)))) ||
      (!i.val.testBit 7 && i.val.testBit 6 && i.val.testBit 5 && !i.val.testBit 4 &&
        (!i.val.testBit 3 && (i.val.testBit 2 || i.val.testBit 1 || i.val.testBit 0) &&
          !(i.val.testBit 2 && i.val.testBit 1 && i.val.testBit 0)))) = Model.isHex i.val := by decide

lemma bridge_lead2 : ∀ i : Fin 256,
    (i.val.testBit 7 && i.val.testBit 6 && !i.val.testBit 5 &&
      !(!i.val.testBit 2 && !i.val.testBit 1 && !i.val.testBit 3 && !i.val.testBit 4)) =
      Model.isLead2 i.val := by decide

lemma bridge_lead4_disjF0 : ∀ i : Fin 256,
    ((i.val == 240) &&
      !(i.val.testBit 7 && i.val.testBit 6 && i.val.testBit 5 && i.val.testBit 4 &&
        !i.val.testBit 3 && !i.val.testBit 2)) = false := by decide

lemma bridge_lead4 : ∀ i : Fin 256,
    (i.val.testBit 7 && i.val.testBit 6 && i.val.testBit 5 && i.val.testBit 4 &&
      !i.val.testBit 3 && !i.val.testBit 2 && !(i.val == 240)) = Model.isLead4 i.val := by decide

end ByteClass
end Solution.JSONExtract
