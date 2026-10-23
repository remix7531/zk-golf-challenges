import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.LenFlags
import Solution.JSONExtract.Anchors
import Solution.JSONExtract.Acceptance
import Solution.JSONExtract.SlotPins
import Solution.JSONExtract.Step
import Solution.JSONExtract.MainTheorems

/-!
# Evaluating the gadget interfaces of `main`

`main` calls every gadget on a *struct literal* built from its own witness
vectors.  Peeling the spine leaves each child's `Assumptions` / `Spec` applied
to `eval env <that literal>`; these lemmas push the evaluation through the
literal, so the assembly below works with the gadget's own wires and no
`circuit_norm` ever touches a 1024-entry vector.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSt nSub nClaims)
open Witness (slots)

variable {env : Environment (F circomPrime)}

/-- A `ProvableType`'s prover value is its verifier value, so the two `eval`s agree. -/
lemma eval_prover {M : TypeMap} [ProvableType M] (envP : ProverEnvironment (F circomPrime))
    (b : Var M (F circomPrime)) :
    (eval envP b : M (F circomPrime)) = eval envP.toEnvironment b := by
  simp [circuit_norm]

@[simp] lemma eval_lenFlagsIn (len : E) (v : Vector E flagLen) :
    (eval env ({ len := len, lenFlags := v } : Var LenFlags.Inputs (F circomPrime)))
      = { len := Expression.eval env len, lenFlags := eval env v } := by
  simp [circuit_norm]

@[simp] lemma eval_anchorsIn (accm hexAcc kIdx ofs nMem : E) (st : Vector E nSt)
    (sub : Vector E nSub) (m claim : Vector E nClaims) :
    (eval env ({ accm := accm, st := st, sub := sub, hexAcc := hexAcc, kIdx := kIdx,
                 ofs := ofs, nMem := nMem, m := m,
                 claim := claim } : Var Anchors.Inputs (F circomPrime)))
      = { accm := Expression.eval env accm, st := eval env st, sub := eval env sub,
          hexAcc := Expression.eval env hexAcc, kIdx := Expression.eval env kIdx,
          ofs := Expression.eval env ofs, nMem := Expression.eval env nMem,
          m := eval env m, claim := eval env claim } := by
  simp [circuit_norm]

@[simp] lemma eval_acceptanceIn (st : Vector E nSt) (sub : Vector E nSub) (nMem : E) :
    (eval env ({ st := st, sub := sub, nMem := nMem } : Var Acceptance.Inputs (F circomPrime)))
      = { st := eval env st, sub := eval env sub, nMem := Expression.eval env nMem } := by
  simp [circuit_norm]

@[simp] lemma eval_strSlot {n : ℕ} (p l : E) (b : Vector E n) :
    (eval env ({ present := p, len := l, bytes := b } : Var (StrSlot n) (F circomPrime)))
      = { present := Expression.eval env p, len := Expression.eval env l, bytes := eval env b } := by
  simp [circuit_norm]

@[simp] lemma eval_strSlotPinIn {n : ℕ} (slot : Var (StrSlot n) (F circomPrime)) (p l : E) :
    (eval env ({ slot := slot, present := p,
                 len := l } : Var (StrSlotPin.Inputs n) (F circomPrime)))
      = { slot := eval env slot, present := Expression.eval env p,
          len := Expression.eval env l } := by
  simp [circuit_norm]

@[simp] lemma eval_intSlotPinIn {n : ℕ} (slot : Var (IntSlot n) (F circomPrime)) (p g l : E) :
    (eval env ({ slot := slot, present := p, negative := g,
                 len := l } : Var (IntSlotPin.Inputs n) (F circomPrime)))
      = { slot := eval env slot, present := Expression.eval env p,
          negative := Expression.eval env g, len := Expression.eval env l } := by
  simp [circuit_norm]

@[simp] lemma eval_boolSlotPinIn (slot : Var BoolSlot (F circomPrime)) (p v : E) :
    (eval env ({ slot := slot, present := p,
                 value := v } : Var BoolSlotPin.Inputs (F circomPrime)))
      = { slot := eval env slot, present := Expression.eval env p,
          value := Expression.eval env v } := by
  simp [circuit_norm]

set_option maxHeartbeats 1000000 in
@[simp] lemma eval_stepIn (byte lenFlag accmPrev accmNext hexAccPrev hexAccNext
    kIdxPrev kIdxNext ofsPrev ofsNext nMemPrev nMemNext : E)
    (stPrev stNext : Vector E nSt) (subPrev subNext : Vector E nSub)
    (mPrev mNext claimPrev claimNext : Vector E nClaims)
    (out : Var Output (F circomPrime)) :
    (eval env ({ byte := byte, lenFlag := lenFlag, accmPrev := accmPrev, accmNext := accmNext,
                 stPrev := stPrev, stNext := stNext, subPrev := subPrev, subNext := subNext,
                 hexAccPrev := hexAccPrev, hexAccNext := hexAccNext,
                 kIdxPrev := kIdxPrev, kIdxNext := kIdxNext,
                 mPrev := mPrev, mNext := mNext, claimPrev := claimPrev, claimNext := claimNext,
                 ofsPrev := ofsPrev, ofsNext := ofsNext, nMemPrev := nMemPrev,
                 nMemNext := nMemNext, out := out } : Var Step.Inputs (F circomPrime)))
      = { byte := Expression.eval env byte, lenFlag := Expression.eval env lenFlag,
          accmPrev := Expression.eval env accmPrev, accmNext := Expression.eval env accmNext,
          stPrev := eval env stPrev, stNext := eval env stNext,
          subPrev := eval env subPrev, subNext := eval env subNext,
          hexAccPrev := Expression.eval env hexAccPrev,
          hexAccNext := Expression.eval env hexAccNext,
          kIdxPrev := Expression.eval env kIdxPrev, kIdxNext := Expression.eval env kIdxNext,
          mPrev := eval env mPrev, mNext := eval env mNext,
          claimPrev := eval env claimPrev, claimNext := eval env claimNext,
          ofsPrev := Expression.eval env ofsPrev, ofsNext := Expression.eval env ofsNext,
          nMemPrev := Expression.eval env nMemPrev, nMemNext := Expression.eval env nMemNext,
          out := eval env out } := by
  simp [circuit_norm]

/-! ## Reading the evaluated structs -/

set_option linter.constructorNameAsVariable false in
lemma eval_inputStructP (envP : ProverEnvironment (F circomPrime))
    (inp : Var Input (F circomPrime)) :
    (eval envP inp : Input (F circomPrime))
      = { buffer := eval envP.toEnvironment inp.buffer,
          len := Expression.eval envP.toEnvironment inp.len } := by
  obtain ⟨b, l⟩ := inp
  simp [circuit_norm]

set_option linter.constructorNameAsVariable false in
lemma eval_inputStruct (inp : Var Input (F circomPrime)) :
    (eval env inp : Input (F circomPrime))
      = { buffer := eval env inp.buffer, len := Expression.eval env inp.len } := by
  obtain ⟨b, l⟩ := inp
  simp [circuit_norm]


set_option linter.constructorNameAsVariable false in
lemma eval_outputStruct (o : Var Output (F circomPrime)) :
    (eval env o : Output (F circomPrime))
      = { iss := eval env o.iss, sub := eval env o.sub, aud := eval env o.aud,
          azp := eval env o.azp, hd := eval env o.hd, email := eval env o.email,
          emailVerified := eval env o.emailVerified, nonce := eval env o.nonce,
          atHash := eval env o.atHash, iat := eval env o.iat, exp := eval env o.exp } := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := o
  simp [circuit_norm]

lemma getElem_eval_vec {n : ℕ} (v : Vector E n) (i : ℕ) (hi : i < n) :
    (eval env v : Vector (F circomPrime) n)[i] = Expression.eval env v[i] := by
  rw [CircuitType.eval_var_fields, Vector.getElem_map]

lemma eval_sumOver (sigs : Vector (Var Step.Outputs (F circomPrime)) bufferLen)
    (f : Var Step.Outputs (F circomPrime) → E) :
    Expression.eval env (sumOver sigs f)
      = ∑ i : Fin bufferLen, Expression.eval env (f sigs[i.val]) := by
  rw [sumOver, LenFlags.eval_foldl_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

end Solution.JSONExtract
