import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
import Clean.Circomlib.Comparators
import Solution.JSONExtract.Mul
import Solution.JSONExtract.Model
import Solution.JSONExtract.Rows
import Solution.JSONExtract.ByteClass
import Solution.JSONExtract.OneHot
import Solution.JSONExtract.RouteSlot
import Solution.JSONExtract.SubAutomaton
import Solution.JSONExtract.MainAutomaton
import Solution.JSONExtract.Matcher
import Solution.JSONExtract.ClaimKinds
import Solution.JSONExtract.Emit
import Solution.JSONExtract.CodePoint
import Solution.JSONExtract.KeyIndex
import Solution.JSONExtract.KeyMatchers
import Solution.JSONExtract.ClaimReg
import Solution.JSONExtract.ValueEmit
import Solution.JSONExtract.Offset
import Solution.JSONExtract.ClaimSignals
import Solution.JSONExtract.RouteCells
import Solution.JSONExtract.AsciiCheck
import Solution.JSONExtract.ChannelsLawful
import Solution.JSONExtract.StepSpec
import Solution.JSONExtract.StepInterfaces
import Solution.JSONExtract.StepModel

/-!
# One position of the extraction automaton (`JSONExtract`)

`Step` is the per-byte gadget of the extractor. Given the byte
at a position, the automaton state and registers *before* it, and the
witnessed state and registers *after* it, it checks that the two are related
by the transition relation of `Model.lean` when the position is active
(`i < len`), and that everything is frozen when it is not; it derives the
emission of a decoded code point, drives the key matchers, routes a value
into the output slots, and returns the per-position signals the end pins of
`Main.lean` sum over.

`main` is *glue only*: sixteen operations, all of them subcircuits except one
row (the activity prefix sum) and one witnessed product (`closeQuote`, which
both automata read).  Everything else lives in a gadget of at most nine
operations of its own, each with its own `Spec` and proofs:

| gadget | what it pins |
| --- | --- |
| `ByteClass` | the byte's classes |
| `ClaimKinds` | the claim register is boolean with at most one flag |
| `SubAutomaton` / `MainAutomaton` | the two transition relations |
| `Emit` | the four emission flags |
| `CodePoint` | the decoded code point and the `\uXXXX` accumulator |
| `KeyIndex` | the key events, the key index and its one-hot |
| `KeyMatchers` | the eleven key matchers |
| `ClaimReg` | the claim register update |
| `ValueEmit` | the value characters and the routed value |
| `Offset` | the value offset and its one-hot |
| `ClaimSignals` | the per-claim signals and the member counter |
| `RouteCells` | routing into the ten output slots |
| `AsciiCheck` | a routed string code point is ASCII |
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Circomlib
open Model (nSt nSub nClaims kIdxMax ofsMax St Sub)

namespace Step

open Model.St Model.Sub in
def main (inp : Var Inputs (F circomPrime)) :
    Circuit (F circomPrime) (Var Outputs (F circomPrime)) := do
  let c ← ByteClass.circuit inp.byte
  let stPrev := inp.stPrev
  let subPrev := inp.subPrev
  let claimPrev := inp.claimPrev
  -- the claim register is boolean with at most one flag set
  ClaimKinds.circuit { claimPrev := claimPrev, mPrev := inp.mPrev }
  let kStr := ClaimKinds.kStrE claimPrev
  let kInt := ClaimKinds.kIntE claimPrev
  let kBool := ClaimKinds.kBoolE claimPrev
  let kUnk := ClaimKinds.kUnkE claimPrev
  -- activity: prefix sum of the length flags
  assertZero (inp.accmNext - inp.accmPrev - inp.lenFlag)
  let active := 1 - inp.accmNext
  -- the two automata
  let inStr := stPrev[KEY] + stPrev[STR]
  let closeQuote ← Rows.mul c.bytes.isQuote subPrev[PLAIN]
  SubAutomaton.circuit {
    inStr := inStr, active := active, cls := c, subPrev := subPrev, subNext := inp.subNext }
  MainAutomaton.circuit {
    active := active, closeQuote := closeQuote, cls := c,
    kinds := #v[kStr, kInt, kBool, kUnk], stPrev := stPrev, stNext := inp.stNext }
  -- emission of a decoded code point
  let em ← Emit.circuit {
    inStr := inStr, subPrev := subPrev, isUnescaped := c.classes.isUnescaped,
    isSimpleEsc := c.classes.isSimpleEsc, isHex := c.classes.isHex,
    isCont := c.classes.isCont }
  let emit := em.emitPlain + em.emitEsc + em.emitU + em.emitUtf8
  let escVal := 0x22 * c.bytes.isQuote + 0x5C * c.bytes.isBackslash + 0x2F * c.bytes.isSlash
    + 0x08 * c.bytes.isLowerB + 0x0C * c.bytes.isLowerF + 0x0A * c.bytes.isLowerN
    + 0x0D * c.bytes.isLowerR + 0x09 * c.bytes.isLowerT
  let cpo ← CodePoint.circuit {
    byte := inp.byte, isDigit := c.classes.isDigit, isUpperHex := c.classes.isUpperHex,
    isLowerHex := c.classes.isLowerHex, escVal := escVal, emitPlain := em.emitPlain,
    emitEsc := em.emitEsc, emitU := em.emitU, emitUtf8 := em.emitUtf8,
    inH := subPrev[H1] + subPrev[H2] + subPrev[H3], hexAccPrev := inp.hexAccPrev,
    hexAccNext := inp.hexAccNext, active := active }
  let cp := cpo.cp
  -- key events, key index and the key matchers
  let ki ← KeyIndex.circuit {
    stKeyPrev := stPrev[KEY], stKeyNext := inp.stNext[KEY], closeQuote := closeQuote,
    emit := emit, kIdxPrev := inp.kIdxPrev, kIdxNext := inp.kIdxNext, active := active }
  let km ← KeyMatchers.circuit {
    cp := cp, emit := emit, kIdxOH := ki.kIdxOH, mPrev := inp.mPrev, mNext := inp.mNext,
    keyStart := ki.keyStart, keyClose := ki.keyClose, stKey := stPrev[KEY],
    active := active }
  -- claim register: set at a key close, reset at a key start, held otherwise
  ClaimReg.circuit {
    active := active, keyClose := ki.keyClose, keyStart := ki.keyStart,
    match_ := km.match_, claimPrev := claimPrev, claimNext := inp.claimNext }
  -- value emission
  let ve ← ValueEmit.circuit {
    emit := emit, stStr := stPrev[STR], isDigit := c.classes.isDigit,
    stNum := stPrev[PVAL] + stPrev[NSIGN] + stPrev[NINT], kStrInt := kStr + kInt,
    cp := cp, byte := inp.byte }
  let vEmit := ve.strEmit + ve.digitEmit
  let inVal := 1 - stPrev[PRE] - stPrev[OBJ] - stPrev[KEY] - stPrev[AKEY] - stPrev[PVAL]
    - stPrev[AVAL] - stPrev[SEP] - stPrev[END]
  let ofs ← Offset.circuit {
    ofsPrev := inp.ofsPrev, ofsNext := inp.ofsNext, vEmit := vEmit, inVal := inVal,
    active := active }
  -- the per-position signals and the member counter
  let sig ← ClaimSignals.circuit {
    vEmit := vEmit, claimPrev := claimPrev, stPval := stPrev[PVAL],
    isMinus := c.bytes.isMinus, stT3 := stPrev[T3], isLowerE := c.bytes.isLowerE,
    nMemPrev := inp.nMemPrev, nMemNext := inp.nMemNext, keyStart := ki.keyStart }
  -- routing into the ten string/integer slots
  let o := inp.out
  RouteCells.circuit {
    write := ve.write, valOut := ve.valOut, claimPrev := claimPrev, ofsOH := ofs.ofsOH,
    iss := o.iss.bytes, sub := o.sub.bytes, aud := o.aud.bytes, azp := o.azp.bytes,
    hd := o.hd.bytes, email := o.email.bytes, nonce := o.nonce.bytes,
    atHash := o.atHash.bytes, iat := o.iat.digits, exp := o.exp.digits }
  -- a string claim's code point is ASCII
  AsciiCheck.circuit { cp := cp, write := ve.write, stStr := stPrev[STR] }
  return { match_ := km.match_, vEmitK := sig.vEmitK, minusK := sig.minusK,
           trueK := sig.trueK }

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs Outputs main := by
  elaborate_circuit

/-! ## Peeling the sixteen operations

`circuit_proof_start` still does not converge on `main`, but not because of the
gadget's own structure: `Step.Inputs` carries the whole `Output` (664 slot cells
plus the eleven presence/length blocks), and `circuit_norm` normalises that
`ProvableStruct` into the constraint statement.  The structural peel of
`StepSpec.lean` (`Peel` section) handles the sixteen operations instead: one
rewrite per `do`-block former, keyed on the former rather than on the operation
list, applied to `h_holds` *and* to the goal, so that both come out with the
same child offsets.  The `set` block that follows names each child's input
struct and output block, which keeps the trap of the T4 report (a single `rw`
mentioning a classifier flag `whnf`s the 44-field `varFromOffset`) out of the
way.  What comes out is the sixteen child `Spec`s, in about twenty seconds.

The value-level reading of those `Spec`s is `StepSpec.RowSpec`, and the bridge
to `Model.lean` is `StepModel.lean`: `spec_of_rows` turns the rows into the
gadget's `Spec` and `rows_of_encodes` produces them from the honest prover's
view, so soundness and completeness share every model-level argument. -/

open ChannelsLawful in
/-- `Step.main` performs no channel interaction. The default tactic for the
`requirementsChannelsLawful` field normalizes the unfolded `main`, which does not
terminate on a gadget this size; this walks the `do`-block structurally instead. -/
theorem noChannels (input : Var Inputs (F circomPrime)) : NoChannelsCirc (main input) := by
  unfold main Rows.mul
  -- `with_reducible` keeps a failed alternative from unfolding the child gadgets
  repeat' first
    | with_reducible exact NoChannelsCirc.pure _
    | with_reducible exact NoChannelsCirc.assertZero _
    | with_reducible exact NoChannelsCirc.subcircuit rfl
    | with_reducible exact NoChannelsCirc.subcircuitWithAssertion rfl
    | with_reducible exact NoChannelsCirc.assertion rfl
    | with_reducible refine NoChannelsCirc.bind ?_ fun _ => ?_

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := by
  intro i₀ env input_var input h_input h_assumptions h_holds
  refine ⟨?_, ChannelsLawful.requirements_of_noChannels (noChannels input_var i₀)⟩
  simp +instances only [circuit_norm] at h_input
  dsimp only [Assumptions] at *
  rw [← elaborated.output_eq]
  dsimp +instances only [main, Rows.mul] at *
  dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *
  provable_struct_simp
  simp only [sbind, szero, spure, ssub, ssubA, sassert, obind, opure,
    llzero, llsub, llsubA, llassert, osub, osubA,
    byteClass_localLength, subAutomaton_localLength, mainAutomaton_localLength,
    claimKinds_localLength, Mul.circuit_localLength, emit_localLength, codePoint_localLength,
    keyIndex_localLength, keyMatchers_localLength, claimReg_localLength, valueEmit_localLength,
    offset_localLength, claimSignals_localLength, routeCells_localLength, asciiCheck_localLength,
    Nat.add_zero] at h_holds ⊢
  set CV := ByteClass.circuit.output input_var_byte i₀ with hCVdef
  set CKin : Var ClaimKinds.Inputs (F circomPrime) :=
    { claimPrev := input_var_claimPrev,
      mPrev := input_var_mPrev } with hCKin
  set MQin : Var Mul.Inputs (F circomPrime) :=
    { a := CV.bytes.isQuote,
      b := input_var_subPrev[Sub.PLAIN] } with hMQin
  set MQ := Mul.circuit.output MQin (i₀ + 108) with hMQ
  set SAin : Var SubAutomaton.Inputs (F circomPrime) :=
    { inStr := input_var_stPrev[St.KEY] + input_var_stPrev[St.STR],
      active := 1 - input_var_accmNext, cls := CV, subPrev := input_var_subPrev,
      subNext := input_var_subNext } with hSAin
  set MAin : Var MainAutomaton.Inputs (F circomPrime) :=
    { active := 1 - input_var_accmNext, closeQuote := MQ, cls := CV,
      kinds := #v[ClaimKinds.kStrE input_var_claimPrev, ClaimKinds.kIntE input_var_claimPrev,
        ClaimKinds.kBoolE input_var_claimPrev, ClaimKinds.kUnkE input_var_claimPrev],
      stPrev := input_var_stPrev,
      stNext := input_var_stNext } with hMAin
  set EMin : Var Emit.Inputs (F circomPrime) :=
    { inStr := input_var_stPrev[St.KEY] + input_var_stPrev[St.STR],
      subPrev := input_var_subPrev, isUnescaped := CV.classes.isUnescaped,
      isSimpleEsc := CV.classes.isSimpleEsc, isHex := CV.classes.isHex,
      isCont := CV.classes.isCont } with hEMin
  set EM := Emit.circuit.output EMin (i₀ + 108 + 1 + 49 + 99) with hEM
  set CPin : Var CodePoint.Inputs (F circomPrime) :=
    { byte := input_var_byte, isDigit := CV.classes.isDigit,
      isUpperHex := CV.classes.isUpperHex, isLowerHex := CV.classes.isLowerHex,
      escVal := 34 * CV.bytes.isQuote + 92 * CV.bytes.isBackslash + 47 * CV.bytes.isSlash
        + 8 * CV.bytes.isLowerB + 12 * CV.bytes.isLowerF + 10 * CV.bytes.isLowerN
        + 13 * CV.bytes.isLowerR + 9 * CV.bytes.isLowerT,
      emitPlain := EM.emitPlain, emitEsc := EM.emitEsc, emitU := EM.emitU,
      emitUtf8 := EM.emitUtf8,
      inH := input_var_subPrev[Sub.H1] + input_var_subPrev[Sub.H2] + input_var_subPrev[Sub.H3],
      hexAccPrev := input_var_hexAccPrev, hexAccNext := input_var_hexAccNext,
      active := 1 - input_var_accmNext } with hCPin
  set CP := CodePoint.circuit.output CPin (i₀ + 108 + 1 + 49 + 99 + 8) with hCP
  set KIin : Var KeyIndex.Inputs (F circomPrime) :=
    { stKeyPrev := input_var_stPrev[St.KEY], stKeyNext := input_var_stNext[St.KEY],
      closeQuote := MQ, emit := EM.emitPlain + EM.emitEsc + EM.emitU + EM.emitUtf8,
      kIdxPrev := input_var_kIdxPrev, kIdxNext := input_var_kIdxNext,
      active := 1 - input_var_accmNext } with hKIin
  set KI := KeyIndex.circuit.output KIin (i₀ + 108 + 1 + 49 + 99 + 8 + 8) with hKI
  set KMin : Var KeyMatchers.Inputs (F circomPrime) :=
    { cp := CP.cp, emit := EM.emitPlain + EM.emitEsc + EM.emitU + EM.emitUtf8,
      kIdxOH := KI.kIdxOH, mPrev := input_var_mPrev, mNext := input_var_mNext,
      keyStart := KI.keyStart, keyClose := KI.keyClose, stKey := input_var_stPrev[St.KEY],
      active := 1 - input_var_accmNext } with hKMin
  set KM := KeyMatchers.circuit.output KMin (i₀ + 108 + 1 + 49 + 99 + 8 + 8 + 21) with hKM
  set CRin : Var ClaimReg.Inputs (F circomPrime) :=
    { active := 1 - input_var_accmNext, keyClose := KI.keyClose,
      keyStart := KI.keyStart, match_ := KM.match_, claimPrev := input_var_claimPrev,
      claimNext := input_var_claimNext } with hCRin
  set VEin : Var ValueEmit.Inputs (F circomPrime) :=
    { emit := EM.emitPlain + EM.emitEsc + EM.emitU + EM.emitUtf8,
      stStr := input_var_stPrev[St.STR], isDigit := CV.classes.isDigit,
      stNum := input_var_stPrev[St.PVAL] + input_var_stPrev[St.NSIGN] + input_var_stPrev[St.NINT],
      kStrInt := ClaimKinds.kStrE input_var_claimPrev + ClaimKinds.kIntE input_var_claimPrev,
      cp := CP.cp, byte := input_var_byte } with hVEin
  set VE := ValueEmit.circuit.output VEin
    (i₀ + 108 + 1 + 49 + 99 + 8 + 8 + 21 + 88 + 22) with hVE
  set OFin : Var Offset.Inputs (F circomPrime) :=
    { ofsPrev := input_var_ofsPrev, ofsNext := input_var_ofsNext,
      vEmit := VE.strEmit + VE.digitEmit,
      inVal := 1 - input_var_stPrev[St.PRE] - input_var_stPrev[St.OBJ] - input_var_stPrev[St.KEY]
        - input_var_stPrev[St.AKEY] - input_var_stPrev[St.PVAL] - input_var_stPrev[St.AVAL]
        - input_var_stPrev[St.SEP] - input_var_stPrev[St.END],
      active := 1 - input_var_accmNext } with hOFin
  set OF := Offset.circuit.output OFin
    (i₀ + 108 + 1 + 49 + 99 + 8 + 8 + 21 + 88 + 22 + 5) with hOF
  set SGin : Var ClaimSignals.Inputs (F circomPrime) :=
    { vEmit := VE.strEmit + VE.digitEmit, claimPrev := input_var_claimPrev,
      stPval := input_var_stPrev[St.PVAL], isMinus := CV.bytes.isMinus,
      stT3 := input_var_stPrev[St.T3], isLowerE := CV.bytes.isLowerE,
      nMemPrev := input_var_nMemPrev, nMemNext := input_var_nMemNext,
      keyStart := KI.keyStart } with hSGin
  set SG := ClaimSignals.circuit.output SGin
    (i₀ + 108 + 1 + 49 + 99 + 8 + 8 + 21 + 88 + 22 + 5 + 132) with hSG
  set RCin : Var RouteCells.Inputs (F circomPrime) :=
    { write := VE.write, valOut := VE.valOut, claimPrev := input_var_claimPrev,
      ofsOH := OF.ofsOH, iss := input_var_out_iss_bytes, sub := input_var_out_sub_bytes,
      aud := input_var_out_aud_bytes, azp := input_var_out_azp_bytes, hd := input_var_out_hd_bytes,
      email := input_var_out_email_bytes, nonce := input_var_out_nonce_bytes,
      atHash := input_var_out_atHash_bytes, iat := input_var_out_iat_digits,
      exp := input_var_out_exp_digits } with hRCin
  set ACin : Var AsciiCheck.Inputs (F circomPrime) :=
    { cp := CP.cp, write := VE.write,
      stStr := input_var_stPrev[St.STR] } with hACin
  have evf : ∀ x : Var field (F circomPrime),
      (eval env x : field (F circomPrime)) = Expression.eval env x := by
    intro x; simp [circuit_norm]
  simp only [evf] at h_holds ⊢
  obtain ⟨hBC, hCK, hAccm, hCQ, hSub, hMain, hEmit, hCPs, hKIs, hKMs, hCRs, hVEs, hOFs, hSGs,
    hRC, hAC, -⟩ := h_holds
  obtain ⟨e_byte, e_lenFlag, e_accmPrev, e_accmNext, e_stPrev, e_stNext, e_subPrev, e_subNext,
    e_hexAccPrev, e_hexAccNext, e_kIdxPrev, e_kIdxNext, e_mPrev, e_mNext, e_claimPrev,
    e_claimNext, e_ofsPrev, e_ofsNext, e_nMemPrev, e_nMemNext,
    ⟨-, -, e_iss⟩, ⟨-, -, e_sub⟩, ⟨-, -, e_aud⟩, ⟨-, -, e_azp⟩, ⟨-, -, e_hd⟩, ⟨-, -, e_email⟩,
    ⟨-, -⟩, ⟨-, -, e_nonce⟩, ⟨-, -, e_atHash⟩, ⟨-, -, -, e_iat⟩, -, -, -, e_exp⟩ := h_input
  obtain ⟨hb256, hhex4096, hkidxlt, hofslt⟩ := h_assumptions
  -- the byte classes
  have hclsE : (eval env CV : ByteClass.Outputs (F circomPrime)) = classesOf input_byte.val := by
    have h := hBC (by rw [byteClass_Assumptions, e_byte]; exact hb256)
    rw [byteClass_Spec_iff, e_byte] at h
    exact h
  obtain ⟨cQuote, cBackslash, cSlash, cLowerB, cLowerF, cLowerN, cLowerR, cLowerT, cMinus,
    cLowerE, cUnescaped, cSimpleEsc, cHex, cCont, cDigit, cUpperHex, cLowerHex⟩ := clsFields hclsE
  have vst := eval_vec_getElem e_stPrev
  have vstN := eval_vec_getElem e_stNext
  have vsb := eval_vec_getElem e_subPrev
  have vmP := eval_vec_getElem e_mPrev
  have vclP := eval_vec_getElem e_claimPrev
  have hclsE' : evalCls env CV = classesOf input_byte.val := by rw [← eval_cls']; exact hclsE
  -- the claim register is boolean with at most one flag
  have eCKin : (eval env CKin : ClaimKinds.Inputs (F circomPrime))
      = { claimPrev := input_claimPrev, mPrev := input_mPrev } := by
    rw [hCKin, eval_claimKindsIn, e_claimPrev, e_mPrev]
  have hCKv := hCK trivial
  rw [claimKinds_Spec, eCKin] at hCKv
  simp only [ClaimKinds.Spec] at hCKv
  -- the closing quote
  have eMQin : (eval env MQin : Mul.Inputs (F circomPrime))
      = { a := (classesOf input_byte.val).bytes.isQuote, b := input_subPrev[Sub.PLAIN] } := by
    rw [hMQin, eval_mulIn]
    simp only [Fin.getElem_fin, cQuote, vsb, classesOf]
  have wMQ : Expression.eval env MQ = closeQuote input_byte input_subPrev := by
    have h := hCQ trivial
    rw [Mul.circuit_Spec, eMQin] at h
    simpa only [closeQuote, Fin.getElem_fin] using h
  -- the sub automaton
  have eSAin : (eval env SAin : SubAutomaton.Inputs (F circomPrime))
      = { inStr := inStr input_stPrev, active := 1 - input_accmNext,
          cls := classesOf input_byte.val, subPrev := input_subPrev,
          subNext := input_subNext } := by
    rw [hSAin, eval_subAutoIn]
    simp only [hclsE', e_subPrev, e_subNext, e_accmNext, Expression.eval, eval_sub, eval_add,
      eval_mul, eval_neg, Fin.getElem_fin, vst, inStr]
  have hSubv := hSub trivial
  rw [subAutomaton_Spec, eSAin] at hSubv
  simp only [SubAutomaton.Spec] at hSubv
  -- the main automaton
  have eMAin : (eval env MAin : MainAutomaton.Inputs (F circomPrime))
      = { active := 1 - input_accmNext, closeQuote := closeQuote input_byte input_subPrev,
          cls := classesOf input_byte.val, kinds := kinds input_claimPrev,
          stPrev := input_stPrev, stNext := input_stNext } := by
    rw [hMAin, eval_mainAutoIn, eval_kinds_vec]
    simp only [hclsE', e_stPrev, e_stNext, e_accmNext, wMQ,
      Expression.eval, eval_sub, eval_add, eval_mul, eval_neg,
      Fin.getElem_fin, vclP, kinds, kStr, kInt, kBool, kUnk,
      ClaimKinds.kStrE, ClaimKinds.kIntE, ClaimKinds.kBoolE, ClaimKinds.kUnkE]
  have hMainv := hMain trivial
  rw [mainAutomaton_Spec, eMAin] at hMainv
  simp only [MainAutomaton.Spec] at hMainv
  -- emission
  have eEMin : (eval env EMin : Emit.Inputs (F circomPrime))
      = { inStr := inStr input_stPrev, subPrev := input_subPrev,
          isUnescaped := (classesOf input_byte.val).classes.isUnescaped,
          isSimpleEsc := (classesOf input_byte.val).classes.isSimpleEsc,
          isHex := (classesOf input_byte.val).classes.isHex,
          isCont := (classesOf input_byte.val).classes.isCont } := by
    rw [hEMin, eval_emitIn]
    simp only [e_subPrev, Expression.eval, Fin.getElem_fin, vst, inStr,
      cUnescaped, cSimpleEsc, cHex, cCont, classesOf]
  have hEmitv := hEmit trivial
  rw [emit_Spec, eEMin, eval_emitOut] at hEmitv
  simp only [Emit.Spec] at hEmitv
  obtain ⟨wEP, wEE, wEU, wE8⟩ := hEmitv
  have wEmit : Expression.eval env (EM.emitPlain + EM.emitEsc + EM.emitU + EM.emitUtf8)
      = emit input_byte input_stPrev input_subPrev := by
    simp only [Expression.eval, eval_add, wEP, wEE, wEU, wE8, emit, emitPlain, emitEsc, emitU,
      emitUtf8, Fin.getElem_fin]
  -- the decoded code point and the hex accumulator
  have eCPin : (eval env CPin : CodePoint.Inputs (F circomPrime))
      = { byte := input_byte, isDigit := (classesOf input_byte.val).classes.isDigit,
          isUpperHex := (classesOf input_byte.val).classes.isUpperHex,
          isLowerHex := (classesOf input_byte.val).classes.isLowerHex,
          escVal := escVal input_byte,
          emitPlain := emitPlain input_byte input_stPrev input_subPrev,
          emitEsc := emitEsc input_byte input_stPrev input_subPrev,
          emitU := emitU input_byte input_stPrev input_subPrev,
          emitUtf8 := emitUtf8 input_byte input_stPrev input_subPrev,
          inH := inH input_subPrev, hexAccPrev := input_hexAccPrev,
          hexAccNext := input_hexAccNext, active := 1 - input_accmNext } := by
    rw [hCPin, eval_codePointIn, wEP, wEE, wEU, wE8]
    simp only [e_byte, e_hexAccPrev, e_hexAccNext, e_accmNext, cDigit, cUpperHex, cLowerHex,
      cQuote, cBackslash, cSlash, cLowerB, cLowerF, cLowerN, cLowerR, cLowerT,
      Expression.eval, eval_sub, eval_add, eval_mul, eval_neg, Fin.getElem_fin, vsb,
      classesOf, escVal, emitPlain, emitEsc, emitU, emitUtf8, inH]
  have hCPv := hCPs trivial
  rw [codePoint_Spec, eCPin, eval_codePointOut] at hCPv
  simp only [CodePoint.Spec, CodePoint.HexAccRow, CodePoint.hvOf] at hCPv
  obtain ⟨wCP0, rHexAcc0⟩ := hCPv
  have wCPv : Expression.eval env CP.cp
      = cp input_byte input_stPrev input_subPrev input_hexAccPrev := by
    rw [wCP0]; simp only [cp, hexVal, classesOf]
  have rHexAcc : input_hexAccNext = input_hexAccPrev + (1 - input_accmNext) *
      (inH input_subPrev * (16 * input_hexAccPrev + hexVal input_byte) - input_hexAccPrev) := by
    rw [rHexAcc0]; simp only [hexVal, classesOf]
  -- the key index and the key events
  have eKIin : (eval env KIin : KeyIndex.Inputs (F circomPrime))
      = { stKeyPrev := input_stPrev[St.KEY], stKeyNext := input_stNext[St.KEY],
          closeQuote := closeQuote input_byte input_subPrev,
          emit := emit input_byte input_stPrev input_subPrev,
          kIdxPrev := input_kIdxPrev, kIdxNext := input_kIdxNext,
          active := 1 - input_accmNext } := by
    rw [hKIin, eval_keyIndexIn, wMQ, wEmit]
    simp only [e_kIdxPrev, e_kIdxNext, e_accmNext, Expression.eval, eval_sub, eval_add,
      eval_mul, eval_neg, Fin.getElem_fin, vst, vstN]
  have hKIv := hKIs (by rw [keyIndex_Assumptions, eKIin]; exact hkidxlt)
  rw [keyIndex_Spec, eKIin, eval_keyIndexOut] at hKIv
  simp only [KeyIndex.Spec, KeyIndex.KIdxRow] at hKIv
  obtain ⟨wKS0, wKC0, wKOH, rKIdx⟩ := hKIv
  have wKS : Expression.eval env KI.keyStart = keyStart input_stPrev input_stNext := wKS0
  have wKC : Expression.eval env KI.keyClose
      = keyClose input_byte input_stPrev input_subPrev := wKC0
  -- the key matchers
  have eKMin : (eval env KMin : KeyMatchers.Inputs (F circomPrime))
      = { cp := cp input_byte input_stPrev input_subPrev input_hexAccPrev,
          emit := emit input_byte input_stPrev input_subPrev,
          kIdxOH := ohOf kIdxMax input_kIdxPrev, mPrev := input_mPrev, mNext := input_mNext,
          keyStart := keyStart input_stPrev input_stNext,
          keyClose := keyClose input_byte input_stPrev input_subPrev,
          stKey := input_stPrev[St.KEY], active := 1 - input_accmNext } := by
    rw [hKMin, eval_keyMatchersIn, wCPv, wEmit, wKOH, wKS, wKC]
    simp only [e_mPrev, e_mNext, e_accmNext, Expression.eval, eval_sub, Fin.getElem_fin, vst]
  have hKMv := hKMs trivial
  rw [keyMatchers_Spec, eKMin, eval_keyMatchersOut] at hKMv
  simp only [KeyMatchers.Spec, KeyMatchers.MRow, KeyMatchers.MatchOf, KeyMatchers.eqCp,
    KeyMatchers.kLen] at hKMv
  obtain ⟨rM, wMatch⟩ := hKMv
  -- the claim register
  have eCRin : (eval env CRin : ClaimReg.Inputs (F circomPrime))
      = { active := 1 - input_accmNext, keyClose := keyClose input_byte input_stPrev input_subPrev,
          keyStart := keyStart input_stPrev input_stNext, match_ := eval env KM.match_,
          claimPrev := input_claimPrev, claimNext := input_claimNext } := by
    rw [hCRin, eval_claimRegIn, wKC, wKS]
    simp only [e_claimPrev, e_claimNext, e_accmNext, Expression.eval, eval_sub]
  have rClaim := hCRs trivial
  rw [claimReg_Spec, eCRin] at rClaim
  simp only [ClaimReg.Spec] at rClaim
  -- value emission
  have eVEin : (eval env VEin : ValueEmit.Inputs (F circomPrime))
      = { emit := emit input_byte input_stPrev input_subPrev, stStr := input_stPrev[St.STR],
          isDigit := (classesOf input_byte.val).classes.isDigit,
          stNum := input_stPrev[St.PVAL] + input_stPrev[St.NSIGN] + input_stPrev[St.NINT],
          kStrInt := kStr input_claimPrev + kInt input_claimPrev,
          cp := cp input_byte input_stPrev input_subPrev input_hexAccPrev,
          byte := input_byte } := by
    rw [hVEin, eval_valueEmitIn, wEmit, wCPv]
    simp only [e_byte, cDigit, Expression.eval, eval_add, Fin.getElem_fin, vst, vclP,
      classesOf, kStr, kInt, ClaimKinds.kStrE, ClaimKinds.kIntE]
  have hVEv := hVEs trivial
  rw [valueEmit_Spec, eVEin, eval_valueEmitOut] at hVEv
  simp only [ValueEmit.Spec] at hVEv
  obtain ⟨wSE0, wDE0, wW0, wVO0⟩ := hVEv
  have wSE : Expression.eval env VE.strEmit = strEmit input_byte input_stPrev input_subPrev := wSE0
  have wDE : Expression.eval env VE.digitEmit = digitEmit input_byte input_stPrev := wDE0
  have wW : Expression.eval env VE.write
      = write input_byte input_stPrev input_subPrev input_claimPrev := by
    rw [wW0, wSE, wDE]; simp only [write, vEmit]
  have wVO : Expression.eval env VE.valOut
      = valOut input_byte input_stPrev input_subPrev input_hexAccPrev := by
    rw [wVO0, wSE, wDE]; simp only [valOut]
  have wVEmit : Expression.eval env (VE.strEmit + VE.digitEmit)
      = vEmit input_byte input_stPrev input_subPrev := by
    simp only [Expression.eval, eval_add, wSE, wDE, vEmit]
  -- the value offset
  have eOFin : (eval env OFin : Offset.Inputs (F circomPrime))
      = { ofsPrev := input_ofsPrev, ofsNext := input_ofsNext,
          vEmit := vEmit input_byte input_stPrev input_subPrev, inVal := inVal input_stPrev,
          active := 1 - input_accmNext } := by
    rw [hOFin, eval_offsetIn, wVEmit]
    simp only [e_ofsPrev, e_ofsNext, e_accmNext, Expression.eval, eval_sub, eval_add,
      eval_mul, eval_neg, Fin.getElem_fin, vst, inVal]
  have hOFv := hOFs (by rw [offset_Assumptions, eOFin]; exact hofslt)
  rw [offset_Spec, eOFin, eval_offsetOut] at hOFv
  simp only [Offset.Spec, Offset.OfsRow] at hOFv
  obtain ⟨wOOH, rOfs⟩ := hOFv
  -- the per-position signals and the member counter
  have eSGin : (eval env SGin : ClaimSignals.Inputs (F circomPrime))
      = { vEmit := vEmit input_byte input_stPrev input_subPrev, claimPrev := input_claimPrev,
          stPval := input_stPrev[St.PVAL],
          isMinus := (classesOf input_byte.val).bytes.isMinus, stT3 := input_stPrev[St.T3],
          isLowerE := (classesOf input_byte.val).bytes.isLowerE, nMemPrev := input_nMemPrev,
          nMemNext := input_nMemNext, keyStart := keyStart input_stPrev input_stNext } := by
    rw [hSGin, eval_claimSignalsIn, wVEmit, wKS]
    simp only [e_claimPrev, e_nMemPrev, e_nMemNext, cMinus, cLowerE, Expression.eval,
      Fin.getElem_fin, vst, classesOf]
  have hSGv := hSGs trivial
  rw [claimSignals_Spec, eSGin, eval_claimSignalsOut] at hSGv
  simp only [ClaimSignals.Spec, ClaimSignals.NMemRow] at hSGv
  obtain ⟨wVEK, wMK, wTK, rNMem⟩ := hSGv
  -- routing into the ten slots
  have eRCin : (eval env RCin : RouteCells.Inputs (F circomPrime))
      = { write := write input_byte input_stPrev input_subPrev input_claimPrev,
          valOut := valOut input_byte input_stPrev input_subPrev input_hexAccPrev,
          claimPrev := input_claimPrev, ofsOH := ohOf ofsMax input_ofsPrev,
          iss := input_out_iss_bytes, sub := input_out_sub_bytes, aud := input_out_aud_bytes,
          azp := input_out_azp_bytes, hd := input_out_hd_bytes, email := input_out_email_bytes,
          nonce := input_out_nonce_bytes, atHash := input_out_atHash_bytes,
          iat := input_out_iat_digits, exp := input_out_exp_digits } := by
    rw [hRCin, eval_routeCellsIn, wW, wVO, wOOH, e_claimPrev, e_iss, e_sub, e_aud, e_azp, e_hd,
      e_email, e_nonce, e_atHash, e_iat, e_exp]
  have rRoute := hRC trivial
  rw [routeCells_Spec, eRCin] at rRoute
  simp only [RouteCells.Spec, RouteCells.selected, RouteCells.existsIn] at rRoute
  -- the ASCII check
  have eACin : (eval env ACin : AsciiCheck.Inputs (F circomPrime))
      = { cp := cp input_byte input_stPrev input_subPrev input_hexAccPrev,
          write := write input_byte input_stPrev input_subPrev input_claimPrev,
          stStr := input_stPrev[St.STR] } := by
    rw [hACin, eval_asciiCheckIn, wCPv, wW]
    simp only [Fin.getElem_fin, vst]
  have hcplt : (cp input_byte input_stPrev input_subPrev input_hexAccPrev).val < 2 ^ 16 :=
    cp_val_lt input_byte input_stPrev input_subPrev input_hexAccPrev hb256
      hMainv.1 hMainv.2.1 hSubv.1 hSubv.2.1 hhex4096
  have rAscii := hAC (by rw [asciiCheck_Assumptions, eACin]; exact hcplt)
  rw [asciiCheck_Spec, eACin] at rAscii
  simp only [AsciiCheck.Spec] at rAscii
  -- the activity row, at the value level
  have rAccm : input_accmNext = input_accmPrev + input_lenFlag := by
    simp only [Expression.eval, eval_sub, e_accmNext, e_accmPrev, e_lenFlag] at hAccm
    linear_combination hAccm
  -- the sixteen child `Spec`s are exactly the rows `StepModel` reads
  rw [eval_stepOut]
  refine spec_of_rows hb256 ?_ _
  refine ⟨hCKv.1, hCKv.2.1, hCKv.2.2, rAccm, hSubv.1, hSubv.2.1, hSubv.2.2, hMainv.1,
    hMainv.2.1, hMainv.2.2, rHexAcc, hkidxlt, rKIdx, rM, wMatch, rClaim, hofslt, rOfs, wVEK,
    wMK, wTK, rNMem, ?_, ?_, rAscii⟩
  · simp only [selected]
    linear_combination rRoute.1
  · simp only [existsIn]
    linear_combination rRoute.2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions
      (fun _ _ _ => True) := by
  intro i₀ env input_var h_env input h_input h_assumptions
  refine ⟨?_, trivial⟩
  simp +instances only [circuit_norm] at h_input
  dsimp only [ProverAssumptions] at *
  dsimp +instances only [main, Rows.mul] at *
  dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *
  provable_struct_simp
  simp only [cbind, czero, cpure, csub, csubA, cassert, wbind, wzero, wpure, wsub, wsubA,
    wassert, llzero, llsub, llsubA, llassert, osub, osubA,
    byteClass_localLength, subAutomaton_localLength, mainAutomaton_localLength,
    claimKinds_localLength, Mul.circuit_localLength, emit_localLength, codePoint_localLength,
    keyIndex_localLength, keyMatchers_localLength, claimReg_localLength, valueEmit_localLength,
    offset_localLength, claimSignals_localLength, routeCells_localLength, asciiCheck_localLength,
    Nat.add_zero] at h_env ⊢
  set CV := ByteClass.circuit.output input_var_byte i₀ with hCVdef
  set CKin : Var ClaimKinds.Inputs (F circomPrime) :=
    { claimPrev := input_var_claimPrev,
      mPrev := input_var_mPrev } with hCKin
  set MQin : Var Mul.Inputs (F circomPrime) :=
    { a := CV.bytes.isQuote,
      b := input_var_subPrev[Sub.PLAIN] } with hMQin
  set MQ := Mul.circuit.output MQin (i₀ + 108) with hMQ
  set SAin : Var SubAutomaton.Inputs (F circomPrime) :=
    { inStr := input_var_stPrev[St.KEY] + input_var_stPrev[St.STR],
      active := 1 - input_var_accmNext, cls := CV, subPrev := input_var_subPrev,
      subNext := input_var_subNext } with hSAin
  set MAin : Var MainAutomaton.Inputs (F circomPrime) :=
    { active := 1 - input_var_accmNext, closeQuote := MQ, cls := CV,
      kinds := #v[ClaimKinds.kStrE input_var_claimPrev, ClaimKinds.kIntE input_var_claimPrev,
        ClaimKinds.kBoolE input_var_claimPrev, ClaimKinds.kUnkE input_var_claimPrev],
      stPrev := input_var_stPrev,
      stNext := input_var_stNext } with hMAin
  set EMin : Var Emit.Inputs (F circomPrime) :=
    { inStr := input_var_stPrev[St.KEY] + input_var_stPrev[St.STR],
      subPrev := input_var_subPrev, isUnescaped := CV.classes.isUnescaped,
      isSimpleEsc := CV.classes.isSimpleEsc, isHex := CV.classes.isHex,
      isCont := CV.classes.isCont } with hEMin
  set EM := Emit.circuit.output EMin (i₀ + 108 + 1 + 49 + 99) with hEM
  set CPin : Var CodePoint.Inputs (F circomPrime) :=
    { byte := input_var_byte, isDigit := CV.classes.isDigit,
      isUpperHex := CV.classes.isUpperHex, isLowerHex := CV.classes.isLowerHex,
      escVal := 34 * CV.bytes.isQuote + 92 * CV.bytes.isBackslash + 47 * CV.bytes.isSlash
        + 8 * CV.bytes.isLowerB + 12 * CV.bytes.isLowerF + 10 * CV.bytes.isLowerN
        + 13 * CV.bytes.isLowerR + 9 * CV.bytes.isLowerT,
      emitPlain := EM.emitPlain, emitEsc := EM.emitEsc, emitU := EM.emitU,
      emitUtf8 := EM.emitUtf8,
      inH := input_var_subPrev[Sub.H1] + input_var_subPrev[Sub.H2] + input_var_subPrev[Sub.H3],
      hexAccPrev := input_var_hexAccPrev, hexAccNext := input_var_hexAccNext,
      active := 1 - input_var_accmNext } with hCPin
  set CP := CodePoint.circuit.output CPin (i₀ + 108 + 1 + 49 + 99 + 8) with hCP
  set KIin : Var KeyIndex.Inputs (F circomPrime) :=
    { stKeyPrev := input_var_stPrev[St.KEY], stKeyNext := input_var_stNext[St.KEY],
      closeQuote := MQ, emit := EM.emitPlain + EM.emitEsc + EM.emitU + EM.emitUtf8,
      kIdxPrev := input_var_kIdxPrev, kIdxNext := input_var_kIdxNext,
      active := 1 - input_var_accmNext } with hKIin
  set KI := KeyIndex.circuit.output KIin (i₀ + 108 + 1 + 49 + 99 + 8 + 8) with hKI
  set KMin : Var KeyMatchers.Inputs (F circomPrime) :=
    { cp := CP.cp, emit := EM.emitPlain + EM.emitEsc + EM.emitU + EM.emitUtf8,
      kIdxOH := KI.kIdxOH, mPrev := input_var_mPrev, mNext := input_var_mNext,
      keyStart := KI.keyStart, keyClose := KI.keyClose, stKey := input_var_stPrev[St.KEY],
      active := 1 - input_var_accmNext } with hKMin
  set KM := KeyMatchers.circuit.output KMin (i₀ + 108 + 1 + 49 + 99 + 8 + 8 + 21) with hKM
  set CRin : Var ClaimReg.Inputs (F circomPrime) :=
    { active := 1 - input_var_accmNext, keyClose := KI.keyClose,
      keyStart := KI.keyStart, match_ := KM.match_, claimPrev := input_var_claimPrev,
      claimNext := input_var_claimNext } with hCRin
  set VEin : Var ValueEmit.Inputs (F circomPrime) :=
    { emit := EM.emitPlain + EM.emitEsc + EM.emitU + EM.emitUtf8,
      stStr := input_var_stPrev[St.STR], isDigit := CV.classes.isDigit,
      stNum := input_var_stPrev[St.PVAL] + input_var_stPrev[St.NSIGN] + input_var_stPrev[St.NINT],
      kStrInt := ClaimKinds.kStrE input_var_claimPrev + ClaimKinds.kIntE input_var_claimPrev,
      cp := CP.cp, byte := input_var_byte } with hVEin
  set VE := ValueEmit.circuit.output VEin
    (i₀ + 108 + 1 + 49 + 99 + 8 + 8 + 21 + 88 + 22) with hVE
  set OFin : Var Offset.Inputs (F circomPrime) :=
    { ofsPrev := input_var_ofsPrev, ofsNext := input_var_ofsNext,
      vEmit := VE.strEmit + VE.digitEmit,
      inVal := 1 - input_var_stPrev[St.PRE] - input_var_stPrev[St.OBJ] - input_var_stPrev[St.KEY]
        - input_var_stPrev[St.AKEY] - input_var_stPrev[St.PVAL] - input_var_stPrev[St.AVAL]
        - input_var_stPrev[St.SEP] - input_var_stPrev[St.END],
      active := 1 - input_var_accmNext } with hOFin
  set OF := Offset.circuit.output OFin
    (i₀ + 108 + 1 + 49 + 99 + 8 + 8 + 21 + 88 + 22 + 5) with hOF
  set SGin : Var ClaimSignals.Inputs (F circomPrime) :=
    { vEmit := VE.strEmit + VE.digitEmit, claimPrev := input_var_claimPrev,
      stPval := input_var_stPrev[St.PVAL], isMinus := CV.bytes.isMinus,
      stT3 := input_var_stPrev[St.T3], isLowerE := CV.bytes.isLowerE,
      nMemPrev := input_var_nMemPrev, nMemNext := input_var_nMemNext,
      keyStart := KI.keyStart } with hSGin
  set SG := ClaimSignals.circuit.output SGin
    (i₀ + 108 + 1 + 49 + 99 + 8 + 8 + 21 + 88 + 22 + 5 + 132) with hSG
  set RCin : Var RouteCells.Inputs (F circomPrime) :=
    { write := VE.write, valOut := VE.valOut, claimPrev := input_var_claimPrev,
      ofsOH := OF.ofsOH, iss := input_var_out_iss_bytes, sub := input_var_out_sub_bytes,
      aud := input_var_out_aud_bytes, azp := input_var_out_azp_bytes, hd := input_var_out_hd_bytes,
      email := input_var_out_email_bytes, nonce := input_var_out_nonce_bytes,
      atHash := input_var_out_atHash_bytes, iat := input_var_out_iat_digits,
      exp := input_var_out_exp_digits } with hRCin
  set ACin : Var AsciiCheck.Inputs (F circomPrime) :=
    { cp := CP.cp, write := VE.write,
      stStr := input_var_stPrev[St.STR] } with hACin
  simp only [CircuitType.eval_expression_prover_to_verifier,
    CircuitType.eval_expression_prover_to_verifier'] at h_env ⊢
  have evf : ∀ x : Var field (F circomPrime),
      (eval env.toEnvironment x : field (F circomPrime))
        = Expression.eval env.toEnvironment x := by
    intro x; simp [circuit_norm]
  simp only [evf] at h_env ⊢
  obtain ⟨hBC, -, -, hCQ, -, -, hEmit, hCPs, hKIs, hKMs, -, hVEs, hOFs, hSGs, -, -, -⟩ := h_env
  obtain ⟨e_byte, e_lenFlag, e_accmPrev, e_accmNext, e_stPrev, e_stNext, e_subPrev, e_subNext,
    e_hexAccPrev, e_hexAccNext, e_kIdxPrev, e_kIdxNext, e_mPrev, e_mNext, e_claimPrev,
    e_claimNext, e_ofsPrev, e_ofsNext, e_nMemPrev, e_nMemNext,
    ⟨-, -, e_iss⟩, ⟨-, -, e_sub⟩, ⟨-, -, e_aud⟩, ⟨-, -, e_azp⟩, ⟨-, -, e_hd⟩, ⟨-, -, e_email⟩,
    ⟨-, -⟩, ⟨-, -, e_nonce⟩, ⟨-, -, e_atHash⟩, ⟨-, -, -, e_iat⟩, -, -, -, e_exp⟩ := h_input
  obtain ⟨hb256, r, hw, hE, hacc, hpa⟩ := h_assumptions
  -- the rows the honest prover has to produce
  have hrows := rows_of_encodes' hb256 hw hE hacc hpa
  dsimp only [RowSpec] at hrows
  obtain ⟨hclB, hmB, hkU, hAccmR, hsubB, hsubS, hsubRow, hstB, hstS, hstRow, hHexR, hkidxlt,
    hKIdxR, hMRowR, hMatchR, hClaimR, hofslt, hOfsR, -, -, -, hNMemR, hSelR, hExR, hAscR⟩ :=
    hrows
  simp only [honestOut_match] at hClaimR
  have hhexP : input_hexAccPrev = ((r.hexAcc : ℕ) : F circomPrime) := hE.2.2.1
  have hhexV : input_hexAccPrev.val < 4096 := by
    have hp : r.hexAcc < circomPrime := by
      have h4 : (4096 : ℕ) < circomPrime := by decide
      have := hw.1; omega
    rw [hhexP, ZMod.val_natCast_of_lt hp]
    exact hw.1
  -- the byte classes
  have hclsE : (eval env.toEnvironment CV : ByteClass.Outputs (F circomPrime))
      = classesOf input_byte.val := by
    have h := hBC (by rw [byteClass_Assumptions, e_byte]; exact hb256)
    rw [byteClass_Spec_iff, e_byte] at h
    exact h
  have hclsE' : evalCls env.toEnvironment CV = classesOf input_byte.val := by
    rw [← eval_cls']; exact hclsE
  obtain ⟨cQuote, cBackslash, cSlash, cLowerB, cLowerF, cLowerN, cLowerR, cLowerT, cMinus,
    cLowerE, cUnescaped, cSimpleEsc, cHex, cCont, cDigit, cUpperHex, cLowerHex⟩ := clsFields hclsE
  have vst := eval_vec_getElem e_stPrev
  have vstN := eval_vec_getElem e_stNext
  have vsb := eval_vec_getElem e_subPrev
  have vmP := eval_vec_getElem e_mPrev
  have vclP := eval_vec_getElem e_claimPrev
  -- the child input structures, at the value level
  have eCKin : (eval env.toEnvironment CKin : ClaimKinds.Inputs (F circomPrime))
      = { claimPrev := input_claimPrev, mPrev := input_mPrev } := by
    rw [hCKin, eval_claimKindsIn, e_claimPrev, e_mPrev]
  have eMQin : (eval env.toEnvironment MQin : Mul.Inputs (F circomPrime))
      = { a := (classesOf input_byte.val).bytes.isQuote, b := input_subPrev[Sub.PLAIN] } := by
    rw [hMQin, eval_mulIn]
    simp only [Fin.getElem_fin, cQuote, vsb, classesOf]
  have wMQ : Expression.eval env.toEnvironment MQ = closeQuote input_byte input_subPrev := by
    have h := hCQ trivial
    rw [Mul.circuit_Spec, eMQin] at h
    simpa only [closeQuote, Fin.getElem_fin] using h
  have eSAin : (eval env.toEnvironment SAin : SubAutomaton.Inputs (F circomPrime))
      = { inStr := inStr input_stPrev, active := 1 - input_accmNext,
          cls := classesOf input_byte.val, subPrev := input_subPrev,
          subNext := input_subNext } := by
    rw [hSAin, eval_subAutoIn]
    simp only [hclsE', e_subPrev, e_subNext, e_accmNext, Expression.eval, eval_sub, eval_add,
      eval_mul, eval_neg, Fin.getElem_fin, vst, inStr]
  have eMAin : (eval env.toEnvironment MAin : MainAutomaton.Inputs (F circomPrime))
      = { active := 1 - input_accmNext, closeQuote := closeQuote input_byte input_subPrev,
          cls := classesOf input_byte.val, kinds := kinds input_claimPrev,
          stPrev := input_stPrev, stNext := input_stNext } := by
    rw [hMAin, eval_mainAutoIn, eval_kinds_vec]
    simp only [hclsE', e_stPrev, e_stNext, e_accmNext, wMQ,
      Expression.eval, eval_sub, eval_add, eval_mul, eval_neg,
      Fin.getElem_fin, vclP, kinds, kStr, kInt, kBool, kUnk,
      ClaimKinds.kStrE, ClaimKinds.kIntE, ClaimKinds.kBoolE, ClaimKinds.kUnkE]
  have eEMin : (eval env.toEnvironment EMin : Emit.Inputs (F circomPrime))
      = { inStr := inStr input_stPrev, subPrev := input_subPrev,
          isUnescaped := (classesOf input_byte.val).classes.isUnescaped,
          isSimpleEsc := (classesOf input_byte.val).classes.isSimpleEsc,
          isHex := (classesOf input_byte.val).classes.isHex,
          isCont := (classesOf input_byte.val).classes.isCont } := by
    rw [hEMin, eval_emitIn]
    simp only [e_subPrev, Expression.eval, Fin.getElem_fin, vst, inStr,
      cUnescaped, cSimpleEsc, cHex, cCont, classesOf]
  have hEmitv := hEmit trivial
  rw [emit_Spec, eEMin, eval_emitOut] at hEmitv
  simp only [Emit.Spec] at hEmitv
  obtain ⟨wEP, wEE, wEU, wE8⟩ := hEmitv
  have wEmit : Expression.eval env.toEnvironment
      (EM.emitPlain + EM.emitEsc + EM.emitU + EM.emitUtf8)
      = emit input_byte input_stPrev input_subPrev := by
    simp only [Expression.eval, eval_add, wEP, wEE, wEU, wE8, emit, emitPlain, emitEsc, emitU,
      emitUtf8, Fin.getElem_fin]
  have eCPin : (eval env.toEnvironment CPin : CodePoint.Inputs (F circomPrime))
      = { byte := input_byte, isDigit := (classesOf input_byte.val).classes.isDigit,
          isUpperHex := (classesOf input_byte.val).classes.isUpperHex,
          isLowerHex := (classesOf input_byte.val).classes.isLowerHex,
          escVal := escVal input_byte,
          emitPlain := emitPlain input_byte input_stPrev input_subPrev,
          emitEsc := emitEsc input_byte input_stPrev input_subPrev,
          emitU := emitU input_byte input_stPrev input_subPrev,
          emitUtf8 := emitUtf8 input_byte input_stPrev input_subPrev,
          inH := inH input_subPrev, hexAccPrev := input_hexAccPrev,
          hexAccNext := input_hexAccNext, active := 1 - input_accmNext } := by
    rw [hCPin, eval_codePointIn, wEP, wEE, wEU, wE8]
    simp only [e_byte, e_hexAccPrev, e_hexAccNext, e_accmNext, cDigit, cUpperHex, cLowerHex,
      cQuote, cBackslash, cSlash, cLowerB, cLowerF, cLowerN, cLowerR, cLowerT,
      Expression.eval, eval_sub, eval_add, eval_mul, eval_neg, Fin.getElem_fin, vsb,
      classesOf, escVal, emitPlain, emitEsc, emitU, emitUtf8, inH]
  have hCPpa : CodePoint.circuit.ProverAssumptions (eval env.toEnvironment CPin) env.data
      env.hint := by
    rw [codePoint_ProverAssumptions, eCPin]
    simp only [CodePoint.HexAccRow, CodePoint.hvOf]
    rw [hHexR]
    simp only [hexVal, classesOf]
  have hCPv := (hCPs hCPpa).1 trivial
  rw [codePoint_Spec, eCPin, eval_codePointOut] at hCPv
  simp only [CodePoint.Spec, CodePoint.HexAccRow, CodePoint.hvOf] at hCPv
  have wCPv : Expression.eval env.toEnvironment CP.cp
      = cp input_byte input_stPrev input_subPrev input_hexAccPrev := by
    rw [hCPv.1]; simp only [cp, hexVal, classesOf]
  have eKIin : (eval env.toEnvironment KIin : KeyIndex.Inputs (F circomPrime))
      = { stKeyPrev := input_stPrev[St.KEY], stKeyNext := input_stNext[St.KEY],
          closeQuote := closeQuote input_byte input_subPrev,
          emit := emit input_byte input_stPrev input_subPrev,
          kIdxPrev := input_kIdxPrev, kIdxNext := input_kIdxNext,
          active := 1 - input_accmNext } := by
    rw [hKIin, eval_keyIndexIn, wMQ, wEmit]
    simp only [e_kIdxPrev, e_kIdxNext, e_accmNext, Expression.eval, eval_sub, eval_add,
      eval_mul, eval_neg, Fin.getElem_fin, vst, vstN]
  have hKIpa : KeyIndex.circuit.ProverAssumptions (eval env.toEnvironment KIin) env.data
      env.hint := by
    rw [keyIndex_ProverAssumptions, eKIin]
    exact ⟨hkidxlt, hKIdxR⟩
  have hKIv := (hKIs hKIpa).1 (by rw [keyIndex_Assumptions, eKIin]; exact hkidxlt)
  rw [keyIndex_Spec, eKIin, eval_keyIndexOut] at hKIv
  simp only [KeyIndex.Spec, KeyIndex.KIdxRow] at hKIv
  obtain ⟨wKS0, wKC0, wKOH, -⟩ := hKIv
  have wKS : Expression.eval env.toEnvironment KI.keyStart
      = keyStart input_stPrev input_stNext := wKS0
  have wKC : Expression.eval env.toEnvironment KI.keyClose
      = keyClose input_byte input_stPrev input_subPrev := wKC0
  have eKMin : (eval env.toEnvironment KMin : KeyMatchers.Inputs (F circomPrime))
      = { cp := cp input_byte input_stPrev input_subPrev input_hexAccPrev,
          emit := emit input_byte input_stPrev input_subPrev,
          kIdxOH := ohOf kIdxMax input_kIdxPrev, mPrev := input_mPrev, mNext := input_mNext,
          keyStart := keyStart input_stPrev input_stNext,
          keyClose := keyClose input_byte input_stPrev input_subPrev,
          stKey := input_stPrev[St.KEY], active := 1 - input_accmNext } := by
    rw [hKMin, eval_keyMatchersIn, wCPv, wEmit, wKOH, wKS, wKC]
    simp only [e_mPrev, e_mNext, e_accmNext, Expression.eval, eval_sub, Fin.getElem_fin, vst]
  have hKMpa : KeyMatchers.circuit.ProverAssumptions (eval env.toEnvironment KMin) env.data
      env.hint := by
    rw [keyMatchers_ProverAssumptions, eKMin]
    exact hMRowR
  have hKMv := (hKMs hKMpa).1 trivial
  rw [keyMatchers_Spec, eKMin, eval_keyMatchersOut] at hKMv
  simp only [KeyMatchers.Spec, KeyMatchers.MRow, KeyMatchers.MatchOf, KeyMatchers.eqCp,
    KeyMatchers.kLen] at hKMv
  have wMatch := hKMv.2
  have eCRin : (eval env.toEnvironment CRin : ClaimReg.Inputs (F circomPrime))
      = { active := 1 - input_accmNext, keyClose := keyClose input_byte input_stPrev input_subPrev,
          keyStart := keyStart input_stPrev input_stNext,
          match_ := eval env.toEnvironment KM.match_,
          claimPrev := input_claimPrev, claimNext := input_claimNext } := by
    rw [hCRin, eval_claimRegIn, wKC, wKS]
    simp only [e_claimPrev, e_claimNext, e_accmNext, Expression.eval, eval_sub]
  have eVEin : (eval env.toEnvironment VEin : ValueEmit.Inputs (F circomPrime))
      = { emit := emit input_byte input_stPrev input_subPrev, stStr := input_stPrev[St.STR],
          isDigit := (classesOf input_byte.val).classes.isDigit,
          stNum := input_stPrev[St.PVAL] + input_stPrev[St.NSIGN] + input_stPrev[St.NINT],
          kStrInt := kStr input_claimPrev + kInt input_claimPrev,
          cp := cp input_byte input_stPrev input_subPrev input_hexAccPrev,
          byte := input_byte } := by
    rw [hVEin, eval_valueEmitIn, wEmit, wCPv]
    simp only [e_byte, cDigit, Expression.eval, eval_add, Fin.getElem_fin, vst, vclP,
      classesOf, kStr, kInt, ClaimKinds.kStrE, ClaimKinds.kIntE]
  have hVEv := hVEs trivial
  rw [valueEmit_Spec, eVEin, eval_valueEmitOut] at hVEv
  simp only [ValueEmit.Spec] at hVEv
  obtain ⟨wSE0, wDE0, wW0, wVO0⟩ := hVEv
  have wSE : Expression.eval env.toEnvironment VE.strEmit
      = strEmit input_byte input_stPrev input_subPrev := wSE0
  have wDE : Expression.eval env.toEnvironment VE.digitEmit
      = digitEmit input_byte input_stPrev := wDE0
  have wW : Expression.eval env.toEnvironment VE.write
      = write input_byte input_stPrev input_subPrev input_claimPrev := by
    rw [wW0, wSE, wDE]; simp only [write, vEmit]
  have wVO : Expression.eval env.toEnvironment VE.valOut
      = valOut input_byte input_stPrev input_subPrev input_hexAccPrev := by
    rw [wVO0, wSE, wDE]; simp only [valOut]
  have wVEmit : Expression.eval env.toEnvironment (VE.strEmit + VE.digitEmit)
      = vEmit input_byte input_stPrev input_subPrev := by
    simp only [Expression.eval, eval_add, wSE, wDE, vEmit]
  have eOFin : (eval env.toEnvironment OFin : Offset.Inputs (F circomPrime))
      = { ofsPrev := input_ofsPrev, ofsNext := input_ofsNext,
          vEmit := vEmit input_byte input_stPrev input_subPrev, inVal := inVal input_stPrev,
          active := 1 - input_accmNext } := by
    rw [hOFin, eval_offsetIn, wVEmit]
    simp only [e_ofsPrev, e_ofsNext, e_accmNext, Expression.eval, eval_sub, eval_add,
      eval_mul, eval_neg, Fin.getElem_fin, vst, inVal]
  have hOFpa : Offset.circuit.ProverAssumptions (eval env.toEnvironment OFin) env.data
      env.hint := by
    rw [offset_ProverAssumptions, eOFin]
    exact ⟨hofslt, hOfsR⟩
  have hOFv := (hOFs hOFpa).1 (by rw [offset_Assumptions, eOFin]; exact hofslt)
  rw [offset_Spec, eOFin, eval_offsetOut] at hOFv
  simp only [Offset.Spec, Offset.OfsRow] at hOFv
  have wOOH := hOFv.1
  have eSGin : (eval env.toEnvironment SGin : ClaimSignals.Inputs (F circomPrime))
      = { vEmit := vEmit input_byte input_stPrev input_subPrev, claimPrev := input_claimPrev,
          stPval := input_stPrev[St.PVAL],
          isMinus := (classesOf input_byte.val).bytes.isMinus, stT3 := input_stPrev[St.T3],
          isLowerE := (classesOf input_byte.val).bytes.isLowerE, nMemPrev := input_nMemPrev,
          nMemNext := input_nMemNext, keyStart := keyStart input_stPrev input_stNext } := by
    rw [hSGin, eval_claimSignalsIn, wVEmit, wKS]
    simp only [e_claimPrev, e_nMemPrev, e_nMemNext, cMinus, cLowerE, Expression.eval,
      Fin.getElem_fin, vst, classesOf]
  have eRCin : (eval env.toEnvironment RCin : RouteCells.Inputs (F circomPrime))
      = { write := write input_byte input_stPrev input_subPrev input_claimPrev,
          valOut := valOut input_byte input_stPrev input_subPrev input_hexAccPrev,
          claimPrev := input_claimPrev, ofsOH := ohOf ofsMax input_ofsPrev,
          iss := input_out_iss_bytes, sub := input_out_sub_bytes, aud := input_out_aud_bytes,
          azp := input_out_azp_bytes, hd := input_out_hd_bytes, email := input_out_email_bytes,
          nonce := input_out_nonce_bytes, atHash := input_out_atHash_bytes,
          iat := input_out_iat_digits, exp := input_out_exp_digits } := by
    rw [hRCin, eval_routeCellsIn, wW, wVO, wOOH, e_claimPrev, e_iss, e_sub, e_aud, e_azp, e_hd,
      e_email, e_nonce, e_atHash, e_iat, e_exp]
  have eACin : (eval env.toEnvironment ACin : AsciiCheck.Inputs (F circomPrime))
      = { cp := cp input_byte input_stPrev input_subPrev input_hexAccPrev,
          write := write input_byte input_stPrev input_subPrev input_claimPrev,
          stStr := input_stPrev[St.STR] } := by
    rw [hACin, eval_asciiCheckIn, wCPv, wW]
    simp only [Fin.getElem_fin, vst]
  have hcplt : (cp input_byte input_stPrev input_subPrev input_hexAccPrev).val < 2 ^ 16 :=
    cp_val_lt input_byte input_stPrev input_subPrev input_hexAccPrev hb256
      hstB hstS hsubB hsubS hhexV
  -- the sixteen obligations
  refine ⟨by rw [byteClass_Assumptions, e_byte]; exact hb256, ⟨trivial, ?_⟩, ?_, trivial,
    ⟨trivial, ?_⟩, ⟨trivial, ?_⟩, trivial, hCPpa, hKIpa, hKMpa, ⟨trivial, ?_⟩, trivial,
    hOFpa, ?_, ⟨trivial, ?_⟩, ⟨?_, ?_⟩, trivial⟩
  · rw [claimKinds_Spec, eCKin]
    exact ⟨hclB, hmB, hkU⟩
  · simp only [Expression.eval, eval_sub, e_accmNext, e_accmPrev, e_lenFlag]
    linear_combination hAccmR
  · rw [subAutomaton_Spec, eSAin]
    exact ⟨hsubB, hsubS, hsubRow⟩
  · rw [mainAutomaton_Spec, eMAin]
    exact ⟨hstB, hstS, hstRow⟩
  · rw [claimReg_Spec, eCRin]
    intro k
    rw [wMatch k]
    exact hClaimR k
  · rw [claimSignals_ProverAssumptions, eSGin]
    exact hNMemR
  · rw [routeCells_Spec, eRCin]
    refine ⟨?_, ?_⟩
    · simp only [RouteCells.selected]
      simp only [selected] at hSelR
      linear_combination hSelR
    · simp only [RouteCells.existsIn]
      simp only [existsIn] at hExR
      linear_combination hExR
  · rw [asciiCheck_Assumptions, eACin]
    exact hcplt
  · rw [asciiCheck_Spec, eACin]
    exact hAscR


def circuit : GeneralFormalCircuit (F circomPrime) Inputs Outputs where
  main; elaborated; Assumptions; Spec; ProverAssumptions; soundness; completeness
  ProverSpec := fun _ _ _ => True
  exposedChannels_eq := by intro _ _ exposed h; simp at h
  requirementsChannelsLawful := fun input offset =>
    ChannelsLawful.requirementsChannelsLawful_of_noChannels (noChannels input offset) _ _

end Step
end Solution.JSONExtract
