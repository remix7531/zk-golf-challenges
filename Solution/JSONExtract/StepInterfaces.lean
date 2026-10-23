import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Clean.Circuit.Loops
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
import Solution.JSONExtract.StepSpec

/-!
# The bundled interfaces of the eleven gadgets `Step` introduced (`JSONExtract`)

`Interfaces.lean` carries the interfaces of the gadgets that predate the
decomposition of `Step` (the byte classifier, the two automata, `Mul`,
`OneHot`, `RouteSlot`, `Matcher`, `LessThan`).  This file does the same for the
eleven gadgets the decomposition introduced, plus the `eval`-pushing lemmas for
their `Inputs` and `Outputs` literals, so that the composition proof in
`Step.lean` never unfolds a child's `main` and never normalises a big vector.
-/

namespace Solution.JSONExtract

open Challenge.Instances.JSONExtract.Interface
open Model (nSt nSub nClaims kIdxMax ofsMax St Sub Claim)

variable {env : Environment (F circomPrime)}

/-! ## `ClaimKinds` -/

@[simp] lemma claimKinds_Assumptions (inp : ClaimKinds.Inputs (F circomPrime)) :
    ClaimKinds.circuit.Assumptions inp = True := rfl

@[simp] lemma claimKinds_Spec (inp : ClaimKinds.Inputs (F circomPrime)) :
    ClaimKinds.circuit.Spec inp = ClaimKinds.Spec inp := rfl

@[simp] lemma claimKinds_localLength (inp : Var ClaimKinds.Inputs (F circomPrime)) :
    ClaimKinds.circuit.localLength inp = 0 := rfl

@[simp] lemma claimKinds_channelsWithRequirements :
    ClaimKinds.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_claimKindsIn (cl m : Vector (Expression (F circomPrime)) nClaims) :
    (eval env ({ claimPrev := cl, mPrev := m } : Var ClaimKinds.Inputs (F circomPrime)))
      = { claimPrev := eval env cl, mPrev := eval env m } := by
  simp [circuit_norm]

/-! ## `Emit` -/

@[simp] lemma emit_Assumptions (inp : Emit.Inputs (F circomPrime)) :
    Emit.circuit.Assumptions inp = True := rfl

@[simp] lemma emit_Spec (inp : Emit.Inputs (F circomPrime)) (o : Emit.Outputs (F circomPrime)) :
    Emit.circuit.Spec inp o = Emit.Spec inp o := rfl

@[simp] lemma emit_localLength (inp : Var Emit.Inputs (F circomPrime)) :
    Emit.circuit.localLength inp = 8 := rfl

@[simp] lemma emit_channelsWithRequirements :
    Emit.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_emitIn (inStr : Expression (F circomPrime))
    (sp : Vector (Expression (F circomPrime)) nSub)
    (u s h c : Expression (F circomPrime)) :
    (eval env ({ inStr := inStr, subPrev := sp, isUnescaped := u, isSimpleEsc := s,
                 isHex := h, isCont := c } : Var Emit.Inputs (F circomPrime)))
      = { inStr := Expression.eval env inStr, subPrev := eval env sp,
          isUnescaped := Expression.eval env u, isSimpleEsc := Expression.eval env s,
          isHex := Expression.eval env h, isCont := Expression.eval env c } := by
  simp [circuit_norm]

@[simp] lemma eval_emitOut (o : Var Emit.Outputs (F circomPrime)) :
    (eval env o : Emit.Outputs (F circomPrime))
      = { emitPlain := Expression.eval env o.emitPlain,
          emitEsc := Expression.eval env o.emitEsc,
          emitU := Expression.eval env o.emitU,
          emitUtf8 := Expression.eval env o.emitUtf8 } := by
  obtain ⟨-, -, -, -⟩ := o
  simp [circuit_norm]

/-! ## `CodePoint` -/

@[simp] lemma codePoint_Assumptions (inp : CodePoint.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) : CodePoint.circuit.Assumptions inp d = True := rfl

@[simp] lemma codePoint_Spec (inp : CodePoint.Inputs (F circomPrime))
    (o : CodePoint.Outputs (F circomPrime)) (d : ProverData (F circomPrime)) :
    CodePoint.circuit.Spec inp o d = CodePoint.Spec inp o := rfl

@[simp] lemma codePoint_ProverAssumptions (inp : CodePoint.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) (h : ProverHint (F circomPrime)) :
    CodePoint.circuit.ProverAssumptions inp d h = CodePoint.HexAccRow inp := rfl

@[simp] lemma codePoint_ProverSpec (inp : CodePoint.Inputs (F circomPrime))
    (o : CodePoint.Outputs (F circomPrime)) (h : ProverHint (F circomPrime)) :
    CodePoint.circuit.ProverSpec inp o h = True := rfl

@[simp] lemma codePoint_localLength (inp : Var CodePoint.Inputs (F circomPrime)) :
    CodePoint.circuit.localLength inp = 8 := rfl

@[simp] lemma codePoint_channelsWithRequirements :
    CodePoint.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_codePointIn (byte d u l e ep ee eu e8 inH hp hn a :
      Expression (F circomPrime)) :
    (eval env ({ byte := byte, isDigit := d, isUpperHex := u, isLowerHex := l, escVal := e,
                 emitPlain := ep, emitEsc := ee, emitU := eu, emitUtf8 := e8, inH := inH,
                 hexAccPrev := hp, hexAccNext := hn,
                 active := a } : Var CodePoint.Inputs (F circomPrime)))
      = { byte := Expression.eval env byte, isDigit := Expression.eval env d,
          isUpperHex := Expression.eval env u, isLowerHex := Expression.eval env l,
          escVal := Expression.eval env e, emitPlain := Expression.eval env ep,
          emitEsc := Expression.eval env ee, emitU := Expression.eval env eu,
          emitUtf8 := Expression.eval env e8, inH := Expression.eval env inH,
          hexAccPrev := Expression.eval env hp, hexAccNext := Expression.eval env hn,
          active := Expression.eval env a } := by
  simp [circuit_norm]

@[simp] lemma eval_codePointOut (o : Var CodePoint.Outputs (F circomPrime)) :
    (eval env o : CodePoint.Outputs (F circomPrime))
      = { cp := Expression.eval env o.cp } := by
  obtain ⟨-⟩ := o
  simp [circuit_norm]

/-! ## `KeyIndex` -/

@[simp] lemma keyIndex_Assumptions (inp : KeyIndex.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) :
    KeyIndex.circuit.Assumptions inp d = KeyIndex.Assumptions inp := rfl

@[simp] lemma keyIndex_Spec (inp : KeyIndex.Inputs (F circomPrime))
    (o : KeyIndex.Outputs (F circomPrime)) (d : ProverData (F circomPrime)) :
    KeyIndex.circuit.Spec inp o d = KeyIndex.Spec inp o := rfl

@[simp] lemma keyIndex_ProverAssumptions (inp : KeyIndex.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) (h : ProverHint (F circomPrime)) :
    KeyIndex.circuit.ProverAssumptions inp d h
      = (KeyIndex.Assumptions inp ∧ KeyIndex.KIdxRow inp) := rfl

@[simp] lemma keyIndex_ProverSpec (inp : KeyIndex.Inputs (F circomPrime))
    (o : KeyIndex.Outputs (F circomPrime)) (h : ProverHint (F circomPrime)) :
    KeyIndex.circuit.ProverSpec inp o h = True := rfl

@[simp] lemma keyIndex_localLength (inp : Var KeyIndex.Inputs (F circomPrime)) :
    KeyIndex.circuit.localLength inp = 21 := rfl

@[simp] lemma keyIndex_channelsWithRequirements :
    KeyIndex.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_keyIndexIn (kp kn cq e ip inx a : Expression (F circomPrime)) :
    (eval env ({ stKeyPrev := kp, stKeyNext := kn, closeQuote := cq, emit := e,
                 kIdxPrev := ip, kIdxNext := inx,
                 active := a } : Var KeyIndex.Inputs (F circomPrime)))
      = { stKeyPrev := Expression.eval env kp, stKeyNext := Expression.eval env kn,
          closeQuote := Expression.eval env cq, emit := Expression.eval env e,
          kIdxPrev := Expression.eval env ip, kIdxNext := Expression.eval env inx,
          active := Expression.eval env a } := by
  simp [circuit_norm]

@[simp] lemma eval_keyIndexOut (o : Var KeyIndex.Outputs (F circomPrime)) :
    (eval env o : KeyIndex.Outputs (F circomPrime))
      = { keyStart := Expression.eval env o.keyStart,
          keyClose := Expression.eval env o.keyClose,
          kIdxOH := eval env o.kIdxOH } := by
  obtain ⟨-, -, -⟩ := o
  simp [circuit_norm]

/-! ## `KeyMatchers` -/

@[simp] lemma keyMatchers_Assumptions (inp : KeyMatchers.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) : KeyMatchers.circuit.Assumptions inp d = True := rfl

@[simp] lemma keyMatchers_Spec (inp : KeyMatchers.Inputs (F circomPrime))
    (o : KeyMatchers.Outputs (F circomPrime)) (d : ProverData (F circomPrime)) :
    KeyMatchers.circuit.Spec inp o d = KeyMatchers.Spec inp o := rfl

@[simp] lemma keyMatchers_ProverAssumptions (inp : KeyMatchers.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) (h : ProverHint (F circomPrime)) :
    KeyMatchers.circuit.ProverAssumptions inp d h = KeyMatchers.MRow inp := rfl

@[simp] lemma keyMatchers_ProverSpec (inp : KeyMatchers.Inputs (F circomPrime))
    (o : KeyMatchers.Outputs (F circomPrime)) (h : ProverHint (F circomPrime)) :
    KeyMatchers.circuit.ProverSpec inp o h = True := rfl

@[simp] lemma keyMatchers_localLength (inp : Var KeyMatchers.Inputs (F circomPrime)) :
    KeyMatchers.circuit.localLength inp = 88 := rfl

@[simp] lemma keyMatchers_channelsWithRequirements :
    KeyMatchers.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_keyMatchersIn (cp e : Expression (F circomPrime))
    (kOH : Vector (Expression (F circomPrime)) kIdxMax)
    (mp mn : Vector (Expression (F circomPrime)) nClaims)
    (ks kc sk a : Expression (F circomPrime)) :
    (eval env ({ cp := cp, emit := e, kIdxOH := kOH, mPrev := mp, mNext := mn, keyStart := ks,
                 keyClose := kc, stKey := sk,
                 active := a } : Var KeyMatchers.Inputs (F circomPrime)))
      = { cp := Expression.eval env cp, emit := Expression.eval env e,
          kIdxOH := eval env kOH, mPrev := eval env mp,
          mNext := eval env mn, keyStart := Expression.eval env ks,
          keyClose := Expression.eval env kc, stKey := Expression.eval env sk,
          active := Expression.eval env a } := by
  simp [circuit_norm]

@[simp] lemma eval_keyMatchersOut (o : Var KeyMatchers.Outputs (F circomPrime)) :
    (eval env o : KeyMatchers.Outputs (F circomPrime))
      = { match_ := eval env o.match_ } := by
  obtain ⟨-⟩ := o
  simp [circuit_norm]

/-! ## `ClaimReg` -/

@[simp] lemma claimReg_Assumptions (inp : ClaimReg.Inputs (F circomPrime)) :
    ClaimReg.circuit.Assumptions inp = True := rfl

@[simp] lemma claimReg_Spec (inp : ClaimReg.Inputs (F circomPrime)) :
    ClaimReg.circuit.Spec inp = ClaimReg.Spec inp := rfl

@[simp] lemma claimReg_localLength (inp : Var ClaimReg.Inputs (F circomPrime)) :
    ClaimReg.circuit.localLength inp = 22 := rfl

@[simp] lemma claimReg_channelsWithRequirements :
    ClaimReg.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_claimRegIn (a kc ks : Expression (F circomPrime))
    (mt cp cn : Vector (Expression (F circomPrime)) nClaims) :
    (eval env ({ active := a, keyClose := kc, keyStart := ks, match_ := mt, claimPrev := cp,
                 claimNext := cn } : Var ClaimReg.Inputs (F circomPrime)))
      = { active := Expression.eval env a, keyClose := Expression.eval env kc,
          keyStart := Expression.eval env ks, match_ := eval env mt,
          claimPrev := eval env cp,
          claimNext := eval env cn } := by
  simp [circuit_norm]

/-! ## `ValueEmit` -/

@[simp] lemma valueEmit_Assumptions (inp : ValueEmit.Inputs (F circomPrime)) :
    ValueEmit.circuit.Assumptions inp = True := rfl

@[simp] lemma valueEmit_Spec (inp : ValueEmit.Inputs (F circomPrime))
    (o : ValueEmit.Outputs (F circomPrime)) : ValueEmit.circuit.Spec inp o = ValueEmit.Spec inp o :=
  rfl

@[simp] lemma valueEmit_localLength (inp : Var ValueEmit.Inputs (F circomPrime)) :
    ValueEmit.circuit.localLength inp = 5 := rfl

@[simp] lemma valueEmit_channelsWithRequirements :
    ValueEmit.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_valueEmitIn (e ss d sn ki cp byte : Expression (F circomPrime)) :
    (eval env ({ emit := e, stStr := ss, isDigit := d, stNum := sn, kStrInt := ki, cp := cp,
                 byte := byte } : Var ValueEmit.Inputs (F circomPrime)))
      = { emit := Expression.eval env e, stStr := Expression.eval env ss,
          isDigit := Expression.eval env d, stNum := Expression.eval env sn,
          kStrInt := Expression.eval env ki, cp := Expression.eval env cp,
          byte := Expression.eval env byte } := by
  simp [circuit_norm]

@[simp] lemma eval_valueEmitOut (o : Var ValueEmit.Outputs (F circomPrime)) :
    (eval env o : ValueEmit.Outputs (F circomPrime))
      = { strEmit := Expression.eval env o.strEmit,
          digitEmit := Expression.eval env o.digitEmit,
          write := Expression.eval env o.write,
          valOut := Expression.eval env o.valOut } := by
  obtain ⟨-, -, -, -⟩ := o
  simp [circuit_norm]

/-! ## `Offset` -/

@[simp] lemma offset_Assumptions (inp : Offset.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) :
    Offset.circuit.Assumptions inp d = Offset.Assumptions inp := rfl

@[simp] lemma offset_Spec (inp : Offset.Inputs (F circomPrime))
    (o : Offset.Outputs (F circomPrime)) (d : ProverData (F circomPrime)) :
    Offset.circuit.Spec inp o d = Offset.Spec inp o := rfl

@[simp] lemma offset_ProverAssumptions (inp : Offset.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) (h : ProverHint (F circomPrime)) :
    Offset.circuit.ProverAssumptions inp d h
      = (Offset.Assumptions inp ∧ Offset.OfsRow inp) := rfl

@[simp] lemma offset_ProverSpec (inp : Offset.Inputs (F circomPrime))
    (o : Offset.Outputs (F circomPrime)) (h : ProverHint (F circomPrime)) :
    Offset.circuit.ProverSpec inp o h = True := rfl

@[simp] lemma offset_localLength (inp : Var Offset.Inputs (F circomPrime)) :
    Offset.circuit.localLength inp = 132 := rfl

@[simp] lemma offset_channelsWithRequirements :
    Offset.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_offsetIn (op on ve iv a : Expression (F circomPrime)) :
    (eval env ({ ofsPrev := op, ofsNext := on, vEmit := ve, inVal := iv,
                 active := a } : Var Offset.Inputs (F circomPrime)))
      = { ofsPrev := Expression.eval env op, ofsNext := Expression.eval env on,
          vEmit := Expression.eval env ve, inVal := Expression.eval env iv,
          active := Expression.eval env a } := by
  simp [circuit_norm]

@[simp] lemma eval_offsetOut (o : Var Offset.Outputs (F circomPrime)) :
    (eval env o : Offset.Outputs (F circomPrime))
      = { ofsOH := eval env o.ofsOH } := by
  obtain ⟨-⟩ := o
  simp [circuit_norm]

/-! ## `ClaimSignals` -/

@[simp] lemma claimSignals_Assumptions (inp : ClaimSignals.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) : ClaimSignals.circuit.Assumptions inp d = True := rfl

@[simp] lemma claimSignals_Spec (inp : ClaimSignals.Inputs (F circomPrime))
    (o : ClaimSignals.Outputs (F circomPrime)) (d : ProverData (F circomPrime)) :
    ClaimSignals.circuit.Spec inp o d = ClaimSignals.Spec inp o := rfl

@[simp] lemma claimSignals_ProverAssumptions (inp : ClaimSignals.Inputs (F circomPrime))
    (d : ProverData (F circomPrime)) (h : ProverHint (F circomPrime)) :
    ClaimSignals.circuit.ProverAssumptions inp d h = ClaimSignals.NMemRow inp := rfl

@[simp] lemma claimSignals_ProverSpec (inp : ClaimSignals.Inputs (F circomPrime))
    (o : ClaimSignals.Outputs (F circomPrime)) (h : ProverHint (F circomPrime)) :
    ClaimSignals.circuit.ProverSpec inp o h = True := rfl

@[simp] lemma claimSignals_localLength (inp : Var ClaimSignals.Inputs (F circomPrime)) :
    ClaimSignals.circuit.localLength inp = 25 := rfl

@[simp] lemma claimSignals_channelsWithRequirements :
    ClaimSignals.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_claimSignalsIn (ve : Expression (F circomPrime))
    (cp : Vector (Expression (F circomPrime)) nClaims)
    (sp im st il np nn ks : Expression (F circomPrime)) :
    (eval env ({ vEmit := ve, claimPrev := cp, stPval := sp, isMinus := im, stT3 := st,
                 isLowerE := il, nMemPrev := np, nMemNext := nn,
                 keyStart := ks } : Var ClaimSignals.Inputs (F circomPrime)))
      = { vEmit := Expression.eval env ve, claimPrev := eval env cp,
          stPval := Expression.eval env sp, isMinus := Expression.eval env im,
          stT3 := Expression.eval env st, isLowerE := Expression.eval env il,
          nMemPrev := Expression.eval env np, nMemNext := Expression.eval env nn,
          keyStart := Expression.eval env ks } := by
  simp [circuit_norm]

@[simp] lemma eval_claimSignalsOut (o : Var ClaimSignals.Outputs (F circomPrime)) :
    (eval env o : ClaimSignals.Outputs (F circomPrime))
      = { vEmitK := eval env o.vEmitK,
          minusK := eval env o.minusK,
          trueK := Expression.eval env o.trueK } := by
  obtain ⟨-, -, -⟩ := o
  simp [circuit_norm]

/-! ## `RouteCells` -/

@[simp] lemma routeCells_Assumptions (inp : RouteCells.Inputs (F circomPrime)) :
    RouteCells.circuit.Assumptions inp = True := rfl

@[simp] lemma routeCells_Spec (inp : RouteCells.Inputs (F circomPrime)) :
    RouteCells.circuit.Spec inp = RouteCells.Spec inp := rfl

@[simp] lemma routeCells_localLength (inp : Var RouteCells.Inputs (F circomPrime)) :
    RouteCells.circuit.localLength inp = 684 := rfl

@[simp] lemma routeCells_channelsWithRequirements :
    RouteCells.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_routeCellsIn (w vo : Expression (F circomPrime))
    (cp : Vector (Expression (F circomPrime)) nClaims)
    (oh : Vector (Expression (F circomPrime)) ofsMax)
    (iss sub : Vector (Expression (F circomPrime)) 32)
    (aud azp : Vector (Expression (F circomPrime)) 128)
    (hd : Vector (Expression (F circomPrime)) 64)
    (email : Vector (Expression (F circomPrime)) 128)
    (nonce atHash : Vector (Expression (F circomPrime)) 64)
    (iat exp : Vector (Expression (F circomPrime)) 12) :
    (eval env ({ write := w, valOut := vo, claimPrev := cp, ofsOH := oh, iss := iss, sub := sub,
                 aud := aud, azp := azp, hd := hd, email := email, nonce := nonce,
                 atHash := atHash, iat := iat,
                 exp := exp } : Var RouteCells.Inputs (F circomPrime)))
      = { write := Expression.eval env w, valOut := Expression.eval env vo,
          claimPrev := eval env cp, ofsOH := eval env oh,
          iss := eval env iss, sub := eval env sub,
          aud := eval env aud, azp := eval env azp,
          hd := eval env hd, email := eval env email,
          nonce := eval env nonce, atHash := eval env atHash,
          iat := eval env iat, exp := eval env exp } := by
  simp [circuit_norm]

/-! ## `AsciiCheck` -/

@[simp] lemma asciiCheck_Assumptions (inp : AsciiCheck.Inputs (F circomPrime)) :
    AsciiCheck.circuit.Assumptions inp = AsciiCheck.Assumptions inp := rfl

@[simp] lemma asciiCheck_Spec (inp : AsciiCheck.Inputs (F circomPrime)) :
    AsciiCheck.circuit.Spec inp = AsciiCheck.Spec inp := rfl

@[simp] lemma asciiCheck_localLength (inp : Var AsciiCheck.Inputs (F circomPrime)) :
    AsciiCheck.circuit.localLength inp = 19 := rfl

@[simp] lemma asciiCheck_channelsWithRequirements :
    AsciiCheck.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma eval_asciiCheckIn (cp w ss : Expression (F circomPrime)) :
    (eval env ({ cp := cp, write := w,
                 stStr := ss } : Var AsciiCheck.Inputs (F circomPrime)))
      = { cp := Expression.eval env cp, write := Expression.eval env w,
          stStr := Expression.eval env ss } := by
  simp [circuit_norm]

/-! ## `SubAutomaton` / `MainAutomaton`: the missing pieces -/

@[simp] lemma subAutomaton_channelsWithRequirements :
    SubAutomaton.circuit.channelsWithRequirements = [] := rfl

@[simp] lemma mainAutomaton_channelsWithRequirements :
    MainAutomaton.circuit.channelsWithRequirements = [] := rfl

/-! ## Reading a vector and the classifier struct pointwise -/

open ByteClass (ind)

/-- A vector `eval` equation, used pointwise. -/
lemma eval_vec_getElem {n : ℕ} {v : Vector (Expression (F circomPrime)) n}
    {w : Vector (F circomPrime) n} (h : (eval env v : Vector (F circomPrime) n) = w)
    (i : ℕ) (hi : i < n) : Expression.eval env (v[i]'hi) = w[i]'hi := by
  rw [← h]; simp [circuit_norm]

/-- The seventeen classifier flags one position reads, from the classifier's
whole-struct `Spec`. -/
lemma clsFields {cv : ByteClass.Outputs (Expression (F circomPrime))} {b : ℕ}
    (h : (eval env cv : ByteClass.Outputs (F circomPrime)) = classesOf b) :
    Expression.eval env cv.bytes.isQuote = ind (b == 0x22) ∧
    Expression.eval env cv.bytes.isBackslash = ind (b == 0x5C) ∧
    Expression.eval env cv.bytes.isSlash = ind (b == 0x2F) ∧
    Expression.eval env cv.bytes.isLowerB = ind (b == 0x62) ∧
    Expression.eval env cv.bytes.isLowerF = ind (b == 0x66) ∧
    Expression.eval env cv.bytes.isLowerN = ind (b == 0x6E) ∧
    Expression.eval env cv.bytes.isLowerR = ind (b == 0x72) ∧
    Expression.eval env cv.bytes.isLowerT = ind (b == 0x74) ∧
    Expression.eval env cv.bytes.isMinus = ind (b == 0x2D) ∧
    Expression.eval env cv.bytes.isLowerE = ind (b == 0x65) ∧
    Expression.eval env cv.classes.isUnescaped = ind (Model.isUnescaped b) ∧
    Expression.eval env cv.classes.isSimpleEsc = ind (Model.isSimpleEsc b) ∧
    Expression.eval env cv.classes.isHex = ind (Model.isHex b) ∧
    Expression.eval env cv.classes.isCont = ind (Model.isCont b) ∧
    Expression.eval env cv.classes.isDigit = ind (Model.isDigit b) ∧
    Expression.eval env cv.classes.isUpperHex = ind (Model.isUpperHex b) ∧
    Expression.eval env cv.classes.isLowerHex = ind (Model.isLowerHex b) := by
  rw [Step.eval_cls'] at h
  exact ⟨congrArg (·.bytes.isQuote) h, congrArg (·.bytes.isBackslash) h,
    congrArg (·.bytes.isSlash) h, congrArg (·.bytes.isLowerB) h,
    congrArg (·.bytes.isLowerF) h, congrArg (·.bytes.isLowerN) h,
    congrArg (·.bytes.isLowerR) h, congrArg (·.bytes.isLowerT) h,
    congrArg (·.bytes.isMinus) h, congrArg (·.bytes.isLowerE) h,
    congrArg (·.classes.isUnescaped) h, congrArg (·.classes.isSimpleEsc) h,
    congrArg (·.classes.isHex) h, congrArg (·.classes.isCont) h,
    congrArg (·.classes.isDigit) h, congrArg (·.classes.isUpperHex) h,
    congrArg (·.classes.isLowerHex) h⟩

/-! ## The gadget's own output block -/

@[simp] lemma eval_stepOut (o : Var Step.Outputs (F circomPrime)) :
    ProvableStruct.eval env o
      = { match_ := eval env o.match_, vEmitK := eval env o.vEmitK,
          minusK := eval env o.minusK, trueK := Expression.eval env o.trueK } := by
  obtain ⟨-, -, -, -⟩ := o
  simp [circuit_norm]

@[simp] lemma eval_stepOut' (o : Var Step.Outputs (F circomPrime)) :
    (eval env o : Step.Outputs (F circomPrime))
      = { match_ := eval env o.match_, vEmitK := eval env o.vEmitK,
          minusK := eval env o.minusK, trueK := Expression.eval env o.trueK } := by
  obtain ⟨-, -, -, -⟩ := o
  simp [circuit_norm]

end Solution.JSONExtract
