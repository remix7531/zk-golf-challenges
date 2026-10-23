import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.Model
import Solution.JSONExtract.Witness

/-!
# Witness-IR program of the extractor (`JSONExtract`)

`Main.main` witnesses the automaton run of `Model.lean`. The trusted obligation
`witgenIsIR` requires every witness generator to be an `.ir` program (plain data),
never a `.native` Lean closure, so the run has to be *unrolled* into a
straight-line list of `let`-steps: the IR has no stateful loop former
(`VExpr.mapRange` bodies only see the running index).

## Block layout

The program is one block of locals per position:

```
locals 0 .. nRegs-1                    registers of `Model.run bytes len 0`
for i = 0 .. bufferLen-1:
  locals sigBase i .. sigBase i+nSigs-1   the per-position signals at position i
  locals regBase (i+1) ..                 registers of `Model.run bytes len (i+1)`
```

with `regBase i = blockSize * i` and `sigBase i = blockSize * i + nRegs`
(`blockSize = nRegs + nSigs`). All locals are u64-sorted (`letU`); the registers
are encoded as

| register | encoding |
|---|---|
| `st`     | `0 .. 26`, the `Fin nSt` value |
| `sub`    | `0 .. 12` |
| `hexAcc` | the nat |
| `kIdx`   | `0 .. 15` |
| `claim`  | `0 .. 10`, `nClaims = 11` for `none` |
| `ofs`    | `0 .. 128` |
| `nMem`   | the nat |
| `m[k]`   | `0`/`1`, one local per claim |

The signals mirror the `let`s of `Model.signals` / `Model.step` one for one, so
that the per-step bridge is a `split_ifs` over the same decision tree. Rejection
is encoded by out-of-range sentinels (`nSt` for "no main transition", `nSub` for
"no sub transition"), which is what `ok`/`adv` test.

The read-out expressions (`stOut`, ..., `outLit`) depend only on the layout, not
on the input, so they are closed constants: built once per process rather than
once per witness site.

`.val` truncates `ZMod.val` to 64 bits, so this program agrees with
`Witness.*Gen` only when the buffer holds bytes and `len ≤ bufferLen`; that is
exactly `ProverAssumptions`, and the bridge lemmas at the end of this file carry
those hypotheses.
-/

namespace Solution.JSONExtract.IR

open Challenge.Instances.JSONExtract.Interface
open Specs.JSON (quote backslash slash lbrace rbrace colon comma minus plus dot
  digit0 digit9 lowerA lowerB lowerE lowerF lowerN lowerR lowerT lowerU upperA upperE upperF
  space tab lf cr backspace formfeed)
open Witgen (FExpr U64Expr BExpr VExpr WitgenIR)
open Model (nSt nSub nClaims ofsMax kIdxMax)
open Witness (slots)

/-- The field of the instance. -/
abbrev Fp := F circomPrime
/-- u64-sorted witness-IR expressions over `Fp`. -/
abbrev UE := U64Expr Fp
/-- Field-sorted witness-IR expressions over `Fp`. -/
abbrev FE := FExpr Fp
/-- Witness-IR conditions over `Fp`. -/
abbrev BE := BExpr Fp

/-! ## Small combinators -/

/-- A u64 constant. -/
def cst (n : ℕ) : UE := .const (UInt64.ofNat n)
/-- Disjunction of conditions (`BExpr` has `not` and `and` only). -/
def bor (x y : BE) : BE := .not (.and (.not x) (.not y))
/-- A condition as the u64 value `0`/`1`. -/
def toU (c : BE) : UE := .ite c (cst 1) (cst 0)
/-- A condition as the field value `0`/`1`. -/
def toF (c : BE) : FE := .ite c (.const 1) (.const 0)
/-- `x = n`. -/
def eqn (x : UE) (n : ℕ) : BE := .neq x (cst n)
/-- `x ≤ n`. -/
def leN (x : UE) (n : ℕ) : BE := .not (.lt (cst n) x)
/-- `n ≤ x`. -/
def geN (x : UE) (n : ℕ) : BE := .not (.lt x (cst n))
/-- `lo ≤ x ∧ x ≤ hi`. -/
def rngN (x : UE) (lo hi : ℕ) : BE := .and (geN x lo) (leN x hi)
/-- `x - n`, as the wrapping u64 addition of `2 ^ 64 - n` (exact for `n ≤ x`). -/
def subN (x : UE) (n : ℕ) : UE := .add x (.const (UInt64.ofNat (2 ^ 64 - n)))
/-- `min x n`. -/
def minN (x : UE) (n : ℕ) : UE := .ite (.lt (cst n) x) (cst n) x
/-- `x` is one of the listed constants. -/
def anyEq (x : UE) : List ℕ → BE
  | [] => .false
  | [n] => eqn x n
  | n :: ns => bor (eqn x n) (anyEq x ns)

/-- A decision chain: the value of the first condition that holds, else `dflt`.
This is the shape of every `if .. then .. else if ..` cascade of `Model.lean`. -/
def chain (ds : List (BE × UE)) (dflt : UE) : UE :=
  ds.foldr (fun p acc => .ite p.1 p.2 acc) dflt

/-! ## Block layout -/

/-- Offset of the main state inside a register block. -/
def rST : ℕ := 0
/-- Offset of the sub state inside a register block. -/
def rSUB : ℕ := 1
/-- Offset of `hexAcc` inside a register block. -/
def rHEXACC : ℕ := 2
/-- Offset of `kIdx` inside a register block. -/
def rKIDX : ℕ := 3
/-- Offset of the claim register inside a register block. -/
def rCLAIM : ℕ := 4
/-- Offset of `ofs` inside a register block. -/
def rOFS : ℕ := 5
/-- Offset of `nMem` inside a register block. -/
def rNMEM : ℕ := 6
/-- Offset of the first key matcher inside a register block. -/
def rM : ℕ := 7
/-- Size of a register block. -/
def nRegs : ℕ := rM + nClaims

/-- The value the claim register takes for `none`. -/
def claimNone : ℕ := nClaims
/-- The value `subNext` takes when the sub automaton rejects. -/
def subNone : ℕ := nSub
/-- The value `stNext` takes when the main automaton rejects. -/
def stNone : ℕ := nSt
/-- The flat cell index standing for "this position routes nothing". -/
def cellNone : ℕ := nClaims * ofsMax

/-! Signal offsets inside a per-position block. They are emitted in dependency
order: every signal only reads the registers of its block and earlier signals. -/

/-- `i < len`: the position is active. -/
def sACTIVE : ℕ := 0
/-- The byte at the position. -/
def sB : ℕ := 1
/-- `Model.isWs` -/ def sWS : ℕ := 2
/-- `Model.isDigit` -/ def sDIGIT : ℕ := 3
/-- `Model.isDigitNz` -/ def sDIGITNZ : ℕ := 4
/-- `Model.isHex` -/ def sHEX : ℕ := 5
/-- `Model.isUnescaped` -/ def sUNESC : ℕ := 6
/-- `Model.isExpLetter` -/ def sEXPL : ℕ := 7
/-- `Model.isSign` -/ def sSIGN : ℕ := 8
/-- `Model.isSimpleEsc` -/ def sSIMPLEESC : ℕ := 9
/-- `Model.isCont` -/ def sCONT : ℕ := 10
/-- `Model.isLead2` -/ def sLEAD2 : ℕ := 11
/-- `Model.isLead3` -/ def sLEAD3 : ℕ := 12
/-- `Model.isLead4` -/ def sLEAD4 : ℕ := 13
/-- `Model.isContA0BF` -/ def sA0BF : ℕ := 14
/-- `Model.isCont809F` -/ def s809F : ℕ := 15
/-- `Model.isCont90BF` -/ def s90BF : ℕ := 16
/-- `Model.isCont808F` -/ def s808F : ℕ := 17
/-- `Model.inStr` of the main state. -/ def sSTRNOW : ℕ := 18
/-- `emitPlain` -/ def sEMITPLAIN : ℕ := 19
/-- `emitEsc` -/ def sEMITESC : ℕ := 20
/-- `emitU` -/ def sEMITU : ℕ := 21
/-- `emitUtf8` -/ def sEMITUTF8 : ℕ := 22
/-- `emit` -/ def sEMIT : ℕ := 23
/-- `Model.hexVal` of the byte. -/ def sHV : ℕ := 24
/-- The emitted code point. -/ def sCP : ℕ := 25
/-- `Model.stepSub`, `subNone` for a rejection. -/ def sSUBN : ℕ := 26
/-- `Model.kindOf` of the claim register (`0` str, `1` int, `2` bool, `3` unknown). -/
def sKIND : ℕ := 27
/-- `Model.afterValue`, `stNone` for a rejection. -/ def sAFTERVAL : ℕ := 28
/-- `Model.stepSt`, `stNone` for a rejection. -/ def sSTN : ℕ := 29
/-- `keyStart` -/ def sKEYSTART : ℕ := 30
/-- `keyClose` -/ def sKEYCLOSE : ℕ := 31
/-- The claim matched by the closing key, `claimNone` if none. -/ def sMATCHIDX : ℕ := 32
/-- `strEmit` -/ def sSTREMIT : ℕ := 33
/-- `digitEmit` -/ def sDIGITEMIT : ℕ := 34
/-- `vEmit` -/ def sVEMIT : ℕ := 35
/-- `write` -/ def sWRITE : ℕ := 36
/-- `valOut` -/ def sVALOUT : ℕ := 37
/-- `minusFlag` -/ def sMINUS : ℕ := 38
/-- `trueDone` -/ def sTRUEDONE : ℕ := 39
/-- The step has a transition (`Model.step` is `some`). -/ def sOK : ℕ := 40
/-- The registers advance: the position is active and the step has a transition. -/
def sADV : ℕ := 41
/-- The flat cell index this position routes to, `cellNone` if none. -/ def sCELLIDX : ℕ := 42
/-- The claim matched here as seen by the output (`claimNone` past `len`). -/
def sMATCHOUT : ℕ := 43
/-- The claim a value is emitted for, `claimNone` if none. -/ def sVEMITC : ℕ := 44
/-- The claim a `-` sign is consumed for, `claimNone` if none. -/ def sMINUSC : ℕ := 45
/-- The claim a `true` literal is completed for, `claimNone` if none. -/ def sTRUEC : ℕ := 46
/-- Number of signal locals per position. -/
def nSigs : ℕ := 47

/-- Locals per position: the signals plus the next register block. -/
def blockSize : ℕ := nRegs + nSigs
/-- First local of the register block holding `Model.run bytes len i`. -/
def regBase (i : ℕ) : ℕ := blockSize * i
/-- First local of the signal block of position `i`. -/
def sigBase (i : ℕ) : ℕ := blockSize * i + nRegs

/-- A register of block `i`. -/
def reg (i off : ℕ) : UE := .localVar (regBase i + off)
/-- A signal of position `i`. -/
def sigl (i off : ℕ) : UE := .localVar (sigBase i + off)

/-! ## Byte classes -/

/-- `Model.isWs` -/ def cWs (b : UE) : BE := anyEq b [space, tab, lf, cr]
/-- `Model.isDigit` -/ def cDigit (b : UE) : BE := rngN b digit0 digit9
/-- `Model.isDigitNz` -/ def cDigitNz (b : UE) : BE := rngN b (digit0 + 1) digit9
/-- `Model.isUpperHex` -/ def cUpperHex (b : UE) : BE := rngN b upperA upperF
/-- `Model.isLowerHex` -/ def cLowerHex (b : UE) : BE := rngN b lowerA lowerF
/-- `Model.isHex` -/ def cHex (b : UE) : BE := bor (cDigit b) (bor (cUpperHex b) (cLowerHex b))
/-- `Model.isUnescaped` -/
def cUnesc (b : UE) : BE :=
  .and (rngN b space 0x7F) (.and (.not (eqn b quote)) (.not (eqn b backslash)))
/-- `Model.isExpLetter` -/ def cExpL (b : UE) : BE := bor (eqn b lowerE) (eqn b upperE)
/-- `Model.isSign` -/ def cSign (b : UE) : BE := bor (eqn b plus) (eqn b minus)
/-- `Model.isSimpleEsc` -/
def cSimpleEsc (b : UE) : BE :=
  anyEq b [quote, backslash, slash, lowerB, lowerF, lowerN, lowerR, lowerT]
/-- `Model.isCont` -/ def cCont (b : UE) : BE := rngN b 0x80 0xBF
/-- `Model.isLead2` -/ def cLead2 (b : UE) : BE := rngN b 0xC2 0xDF
/-- `Model.isLead3` -/ def cLead3 (b : UE) : BE := bor (rngN b 0xE1 0xEC) (rngN b 0xEE 0xEF)
/-- `Model.isLead4` -/ def cLead4 (b : UE) : BE := rngN b 0xF1 0xF3
/-- `Model.isContA0BF` -/ def cA0BF (b : UE) : BE := rngN b 0xA0 0xBF
/-- `Model.isCont809F` -/ def c809F (b : UE) : BE := rngN b 0x80 0x9F
/-- `Model.isCont90BF` -/ def c90BF (b : UE) : BE := rngN b 0x90 0xBF
/-- `Model.isCont808F` -/ def c808F (b : UE) : BE := rngN b 0x80 0x8F

/-- `Model.escVal` -/
def escValE (b : UE) : UE :=
  chain [(eqn b quote, cst quote), (eqn b backslash, cst backslash), (eqn b slash, cst slash),
    (eqn b lowerB, cst backspace), (eqn b lowerF, cst formfeed), (eqn b lowerN, cst lf),
    (eqn b lowerR, cst cr), (eqn b lowerT, cst tab)] (cst 0)

/-- `Model.hexVal` -/
def hexValE (b : UE) : UE :=
  chain [(cDigit b, subN b digit0), (cUpperHex b, subN b (upperA - 10)),
    (cLowerHex b, subN b (lowerA - 10))] (cst 0)

/-- `Model.kindOf (some k)` as a code (`0` str, `1` int, `2` bool). -/
def kindCode (k : Model.Claim) : ℕ :=
  if Model.isStrClaim k then 0 else if Model.isIntClaim k then 1 else 2

/-- `Model.kindOf` of the claim register. -/
def kindE (claim : UE) : UE :=
  (List.finRange nClaims).foldr (fun k acc => .ite (eqn claim k.val) (cst (kindCode k)) acc) (cst 3)

/-- `Model.claimCap` of the claim register (`0` for `none`, where it is unused). -/
def capE (claim : UE) : UE :=
  (List.finRange nClaims).foldr
    (fun k acc => .ite (eqn claim k.val) (cst (Model.claimCap k)) acc) (cst 0)

/-- The `t`-th byte of claim `k`'s name, as a field constant vector (`Model.nameAt`). -/
def nameVec (k : Model.Claim) : Vector Fp kIdxMax :=
  Vector.ofFn fun t => ((Model.nameAt k t.val : ℕ) : Fp)

/-- `Model.nameAt k kIdx`, read out of the constant table. -/
def nameAtE (k : Model.Claim) (kIdx : UE) : UE :=
  .val (.listGet ((nameVec k).toList.map FExpr.const) kIdx)

/-! ## The program -/

/-- The buffer byte at a position, as an IR expression (`0` out of range). -/
def byteAt (input : Var Input Fp) (i : ℕ) : FE :=
  .expr (if h : i < bufferLen then input.buffer[i] else 0)

/-- The claimed length, as a u64-sorted IR expression. -/
def lenE (input : Var Input Fp) : UE := .val (.expr input.len)

/-- The registers of `Model.Regs.init`. -/
def initBlock : List (Witgen.Step Fp) :=
  [ .letU (cst Model.St.PRE.val), .letU (cst Model.Sub.PLAIN.val), .letU (cst 0),
    .letU (cst 0), .letU (cst claimNone), .letU (cst 0), .letU (cst 0) ]
  ++ List.replicate nClaims (Witgen.Step.letU (cst 0))

/-- The signals of position `i` followed by the registers of block `i + 1`. -/
def stepBlock (input : Var Input Fp) (i : ℕ) : List (Witgen.Step Fp) :=
  -- registers of block `i`
  let st : UE := reg i rST
  let sub : UE := reg i rSUB
  let hexAcc : UE := reg i rHEXACC
  let kIdx : UE := reg i rKIDX
  let claim : UE := reg i rCLAIM
  let ofs : UE := reg i rOFS
  let nMem : UE := reg i rNMEM
  let mv : ℕ → UE := fun k => reg i (rM + k)
  -- signals of position `i`
  let g : ℕ → UE := fun o => sigl i o
  let f : ℕ → BE := fun o => .neq (sigl i o) (cst 1)
  let b : UE := g sB
  let kStrUnk : BE := bor (eqn (g sKIND) 0) (eqn (g sKIND) 3)
  let kIntUnk : BE := bor (eqn (g sKIND) 1) (eqn (g sKIND) 3)
  let kBoolUnk : BE := bor (eqn (g sKIND) 2) (eqn (g sKIND) 3)
  let kUnk : BE := eqn (g sKIND) 3
  let inVal : BE := .not (anyEq st [Model.St.PRE.val, Model.St.OBJ.val, Model.St.KEY.val,
    Model.St.AKEY.val, Model.St.PVAL.val, Model.St.AVAL.val, Model.St.SEP.val, Model.St.END.val])
  [ -- `i < len`
    .letU (toU (.lt (cst i) (lenE input))),
    -- the byte
    .letU (.val (byteAt input i)),
    -- byte classes
    .letU (toU (cWs b)), .letU (toU (cDigit b)), .letU (toU (cDigitNz b)),
    .letU (toU (cHex b)), .letU (toU (cUnesc b)), .letU (toU (cExpL b)),
    .letU (toU (cSign b)), .letU (toU (cSimpleEsc b)), .letU (toU (cCont b)),
    .letU (toU (cLead2 b)), .letU (toU (cLead3 b)), .letU (toU (cLead4 b)),
    .letU (toU (cA0BF b)), .letU (toU (c809F b)), .letU (toU (c90BF b)),
    .letU (toU (c808F b)),
    -- `Model.inStr`
    .letU (toU (bor (eqn st Model.St.KEY.val) (eqn st Model.St.STR.val))),
    -- the four emission cases
    .letU (toU (.and (f sSTRNOW) (.and (eqn sub Model.Sub.PLAIN.val) (f sUNESC)))),
    .letU (toU (.and (f sSTRNOW) (.and (eqn sub Model.Sub.ESC.val) (f sSIMPLEESC)))),
    .letU (toU (.and (f sSTRNOW) (.and (eqn sub Model.Sub.H4.val) (f sHEX)))),
    .letU (toU (.and (f sSTRNOW) (.and (eqn sub Model.Sub.C1.val) (f sCONT)))),
    .letU (toU (bor (bor (f sEMITPLAIN) (f sEMITESC)) (bor (f sEMITU) (f sEMITUTF8)))),
    -- the hex digit value and the emitted code point
    .letU (hexValE b),
    .letU (.ite (f sEMITPLAIN) b
      (.ite (f sEMITESC) (escValE b)
        (.ite (f sEMITU) (.add (.mul (cst 16) hexAcc) (g sHV))
          (.ite (f sEMITUTF8) (cst Model.nonAsciiMarker) (cst 0))))),
    -- `Model.stepSub`
    .letU (chain [(.not (f sSTRNOW), cst Model.Sub.PLAIN.val),
      (eqn sub Model.Sub.PLAIN.val,
        chain [(eqn b quote, cst Model.Sub.PLAIN.val), (f sUNESC, cst Model.Sub.PLAIN.val),
          (eqn b backslash, cst Model.Sub.ESC.val), (f sLEAD2, cst Model.Sub.C1.val),
          (eqn b 0xE0, cst Model.Sub.E0s.val), (f sLEAD3, cst Model.Sub.C2.val),
          (eqn b 0xED, cst Model.Sub.EDs.val), (eqn b 0xF0, cst Model.Sub.F0s.val),
          (f sLEAD4, cst Model.Sub.C3.val), (eqn b 0xF4, cst Model.Sub.F4s.val)] (cst subNone)),
      (eqn sub Model.Sub.ESC.val,
        chain [(f sSIMPLEESC, cst Model.Sub.PLAIN.val), (eqn b lowerU, cst Model.Sub.H1.val)]
          (cst subNone)),
      (eqn sub Model.Sub.H1.val, .ite (f sHEX) (cst Model.Sub.H2.val) (cst subNone)),
      (eqn sub Model.Sub.H2.val, .ite (f sHEX) (cst Model.Sub.H3.val) (cst subNone)),
      (eqn sub Model.Sub.H3.val, .ite (f sHEX) (cst Model.Sub.H4.val) (cst subNone)),
      (eqn sub Model.Sub.H4.val, .ite (f sHEX) (cst Model.Sub.PLAIN.val) (cst subNone)),
      (eqn sub Model.Sub.C1.val, .ite (f sCONT) (cst Model.Sub.PLAIN.val) (cst subNone)),
      (eqn sub Model.Sub.C2.val, .ite (f sCONT) (cst Model.Sub.C1.val) (cst subNone)),
      (eqn sub Model.Sub.C3.val, .ite (f sCONT) (cst Model.Sub.C2.val) (cst subNone)),
      (eqn sub Model.Sub.E0s.val, .ite (f sA0BF) (cst Model.Sub.C1.val) (cst subNone)),
      (eqn sub Model.Sub.EDs.val, .ite (f s809F) (cst Model.Sub.C1.val) (cst subNone)),
      (eqn sub Model.Sub.F0s.val, .ite (f s90BF) (cst Model.Sub.C2.val) (cst subNone))]
      (.ite (f s808F) (cst Model.Sub.C2.val) (cst subNone))),
    -- `Model.kindOf` of the claim register
    .letU (kindE claim),
    -- `Model.afterValue`
    .letU (.ite (f sWS) (cst Model.St.AVAL.val)
      (.ite (eqn b comma) (cst Model.St.SEP.val)
        (.ite (eqn b rbrace) (cst Model.St.END.val) (cst stNone)))),
    -- `Model.stepSt`
    .letU (chain [
      (eqn st Model.St.PRE.val,
        chain [(f sWS, cst Model.St.PRE.val), (eqn b lbrace, cst Model.St.OBJ.val)] (cst stNone)),
      (eqn st Model.St.OBJ.val,
        chain [(f sWS, cst Model.St.OBJ.val), (eqn b quote, cst Model.St.KEY.val),
          (eqn b rbrace, cst Model.St.END.val)] (cst stNone)),
      (eqn st Model.St.KEY.val,
        .ite (.and (eqn b quote) (eqn sub Model.Sub.PLAIN.val)) (cst Model.St.AKEY.val)
          (cst Model.St.KEY.val)),
      (eqn st Model.St.AKEY.val,
        chain [(f sWS, cst Model.St.AKEY.val), (eqn b colon, cst Model.St.PVAL.val)] (cst stNone)),
      (eqn st Model.St.PVAL.val,
        chain [(f sWS, cst Model.St.PVAL.val),
          (.and (eqn b quote) kStrUnk, cst Model.St.STR.val),
          (.and (eqn b minus) kIntUnk, cst Model.St.NSIGN.val),
          (.and (eqn b digit0) kIntUnk, cst Model.St.NZERO.val),
          (.and (f sDIGITNZ) kIntUnk, cst Model.St.NINT.val),
          (.and (eqn b lowerT) kBoolUnk, cst Model.St.T1.val),
          (.and (eqn b lowerF) kBoolUnk, cst Model.St.F1.val),
          (.and (eqn b lowerN) kUnk, cst Model.St.N1.val)] (cst stNone)),
      (eqn st Model.St.STR.val,
        .ite (.and (eqn b quote) (eqn sub Model.Sub.PLAIN.val)) (cst Model.St.AVAL.val)
          (cst Model.St.STR.val)),
      (eqn st Model.St.NSIGN.val,
        chain [(eqn b digit0, cst Model.St.NZERO.val), (f sDIGITNZ, cst Model.St.NINT.val)]
          (cst stNone)),
      (eqn st Model.St.NZERO.val,
        chain [(.and (eqn b dot) kUnk, cst Model.St.NDOT.val),
          (.and (f sEXPL) kUnk, cst Model.St.NE.val)] (g sAFTERVAL)),
      (eqn st Model.St.NINT.val,
        chain [(f sDIGIT, cst Model.St.NINT.val), (.and (eqn b dot) kUnk, cst Model.St.NDOT.val),
          (.and (f sEXPL) kUnk, cst Model.St.NE.val)] (g sAFTERVAL)),
      (eqn st Model.St.NDOT.val, .ite (f sDIGIT) (cst Model.St.NFRAC.val) (cst stNone)),
      (eqn st Model.St.NFRAC.val,
        chain [(f sDIGIT, cst Model.St.NFRAC.val), (f sEXPL, cst Model.St.NE.val)] (g sAFTERVAL)),
      (eqn st Model.St.NE.val,
        chain [(f sSIGN, cst Model.St.NESIGN.val), (f sDIGIT, cst Model.St.NEXP.val)] (cst stNone)),
      (eqn st Model.St.NESIGN.val, .ite (f sDIGIT) (cst Model.St.NEXP.val) (cst stNone)),
      (eqn st Model.St.NEXP.val, .ite (f sDIGIT) (cst Model.St.NEXP.val) (g sAFTERVAL)),
      (eqn st Model.St.T1.val, .ite (eqn b lowerR) (cst Model.St.T2.val) (cst stNone)),
      (eqn st Model.St.T2.val, .ite (eqn b lowerU) (cst Model.St.T3.val) (cst stNone)),
      (eqn st Model.St.T3.val, .ite (eqn b lowerE) (cst Model.St.AVAL.val) (cst stNone)),
      (eqn st Model.St.F1.val, .ite (eqn b lowerA) (cst Model.St.F2.val) (cst stNone)),
      (eqn st Model.St.F2.val, .ite (eqn b 0x6C) (cst Model.St.F3.val) (cst stNone)),
      (eqn st Model.St.F3.val, .ite (eqn b 0x73) (cst Model.St.F4.val) (cst stNone)),
      (eqn st Model.St.F4.val, .ite (eqn b lowerE) (cst Model.St.AVAL.val) (cst stNone)),
      (eqn st Model.St.N1.val, .ite (eqn b lowerU) (cst Model.St.N2.val) (cst stNone)),
      (eqn st Model.St.N2.val, .ite (eqn b 0x6C) (cst Model.St.N3.val) (cst stNone)),
      (eqn st Model.St.N3.val, .ite (eqn b 0x6C) (cst Model.St.AVAL.val) (cst stNone)),
      (eqn st Model.St.AVAL.val, g sAFTERVAL),
      (eqn st Model.St.SEP.val,
        chain [(f sWS, cst Model.St.SEP.val), (eqn b quote, cst Model.St.KEY.val)] (cst stNone))]
      (.ite (f sWS) (cst Model.St.END.val) (cst stNone))),
    -- `keyStart`, `keyClose`, and the matched claim
    .letU (toU (.and (eqn (g sSTN) Model.St.KEY.val) (.not (eqn st Model.St.KEY.val)))),
    .letU (toU (.and (.and (eqn st Model.St.KEY.val) (eqn b quote))
      (eqn sub Model.Sub.PLAIN.val))),
    .letU ((List.finRange nClaims).foldr
      (fun k acc => .ite (.and (f sKEYCLOSE)
        (.and (.neq (mv k.val) (cst 1)) (eqn kIdx (Model.claimName k).length)))
        (cst k.val) acc) (cst claimNone)),
    -- the value-emission signals
    .letU (toU (.and (f sEMIT) (eqn st Model.St.STR.val))),
    .letU (toU (.and (f sDIGIT) (bor (eqn st Model.St.PVAL.val)
      (bor (eqn st Model.St.NSIGN.val) (eqn st Model.St.NINT.val))))),
    .letU (toU (bor (f sSTREMIT) (f sDIGITEMIT))),
    .letU (toU (.and (f sVEMIT) (bor (eqn (g sKIND) 0) (eqn (g sKIND) 1)))),
    .letU (.ite (f sSTREMIT) (g sCP) (.ite (f sDIGITEMIT) (subN b digit0) (cst 0))),
    .letU (toU (.and (eqn st Model.St.PVAL.val) (eqn b minus))),
    .letU (toU (.and (eqn st Model.St.T3.val) (eqn b lowerE))),
    -- the step has a transition
    .letU (toU (.and
      (.and (.not (eqn (g sSUBN) subNone)) (.not (eqn (g sSTN) stNone)))
      (.and (bor (.not (f sWRITE)) (bor (eqn claim claimNone) (.lt ofs (capE claim))))
        (bor (.not (.and (f sWRITE) (eqn st Model.St.STR.val))) (.lt (g sCP) (cst 0x80)))))),
    -- the registers advance
    .letU (toU (.and (f sACTIVE) (f sOK))),
    -- the output-facing signals
    .letU (.ite (.and (f sACTIVE) (f sWRITE)) (.add (.mul claim (cst ofsMax)) ofs) (cst cellNone)),
    .letU (.ite (f sACTIVE) (g sMATCHIDX) (cst claimNone)),
    .letU (.ite (.and (f sACTIVE) (f sVEMIT)) claim (cst claimNone)),
    .letU (.ite (.and (f sACTIVE) (f sMINUS)) claim (cst claimNone)),
    .letU (.ite (.and (f sACTIVE) (f sTRUEDONE)) claim (cst claimNone)),
    -- the registers of block `i + 1`
    .letU (.ite (f sADV) (g sSTN) st),
    .letU (.ite (f sADV) (g sSUBN) sub),
    .letU (.ite (f sADV)
      (.ite (bor (eqn sub Model.Sub.H1.val) (bor (eqn sub Model.Sub.H2.val)
          (eqn sub Model.Sub.H3.val)))
        (.add (.mul (cst 16) hexAcc) (g sHV)) (cst 0))
      hexAcc),
    .letU (.ite (f sADV)
      (.ite (eqn st Model.St.KEY.val) (minN (.add kIdx (g sEMIT)) (kIdxMax - 1)) (cst 0))
      kIdx),
    .letU (.ite (f sADV)
      (.ite (f sKEYCLOSE) (g sMATCHIDX)
        (.ite (f sKEYSTART) (cst claimNone) claim))
      claim),
    .letU (.ite (f sADV)
      (minN (.add (.ite inVal ofs (cst 0)) (g sVEMIT)) (ofsMax - 1)) ofs),
    .letU (.ite (f sADV) (.add nMem (g sKEYSTART)) nMem) ]
  ++ (List.finRange nClaims).map (fun k =>
      Witgen.Step.letU (.ite (f sADV)
        (.ite (f sKEYSTART) (cst 1)
          (.ite (eqn st Model.St.KEY.val)
            (toU (.and (.neq (mv k.val) (cst 1))
              (bor (.not (f sEMIT)) (.neq (g sCP) (nameAtE k kIdx)))))
            (cst 0)))
        (mv k.val)))

/-- The program's steps up to (excluding) position `i`. -/
def stepsUpTo (input : Var Input Fp) (i : ℕ) : List (Witgen.Step Fp) :=
  initBlock ++ (List.range i).flatMap (stepBlock input)

/-- The unrolled automaton run: `bufferLen` position blocks after the initial block. -/
def runSteps (input : Var Input Fp) : List (Witgen.Step Fp) := stepsUpTo input bufferLen

/-! ## Read-outs

These depend only on the block layout, so they are closed constants. -/

/-- `Witness.stGen`: the one-hot main state, position-major. -/
def stOut : VExpr Fp (nSt * slots) :=
  .lit (Vector.ofFn fun idx => toF (.neq (reg (idx.val / nSt) rST) (cst (idx.val % nSt))))

/-- `Witness.subGen`: the one-hot sub state, position-major. -/
def subOut : VExpr Fp (nSub * slots) :=
  .lit (Vector.ofFn fun idx => toF (.neq (reg (idx.val / nSub) rSUB) (cst (idx.val % nSub))))

/-- `Witness.mGen`: the key matchers, position-major. -/
def mOut : VExpr Fp (nClaims * slots) :=
  .lit (Vector.ofFn fun idx =>
    toF (.neq (reg (idx.val / nClaims) (rM + idx.val % nClaims)) (cst 1)))

/-- `Witness.claimGen`: the claim register as a one-hot, position-major. -/
def claimOut : VExpr Fp (nClaims * slots) :=
  .lit (Vector.ofFn fun idx =>
    toF (.neq (reg (idx.val / nClaims) rCLAIM) (cst (idx.val % nClaims))))

/-- Read-out of a nat-valued register, one entry per block. -/
def natOut (off : ℕ) : VExpr Fp slots :=
  .lit (Vector.ofFn fun i => (.ofU64 (reg i.val off) : FE))

/-- `Witness.hexAccGen` -/
def hexAccOut : VExpr Fp slots := natOut rHEXACC

/-- `Witness.kIdxGen` -/
def kIdxOut : VExpr Fp slots := natOut rKIDX

/-- `Witness.ofsGen` -/
def ofsOut : VExpr Fp slots := natOut rOFS

/-- `Witness.nMemGen` -/
def nMemOut : VExpr Fp slots := natOut rNMEM

/-- `Witness.lenFlagsGen`: no steps needed, the one-hot of `len`. -/
def lenFlagsOut (input : Var Input Fp) : VExpr Fp slots :=
  .mapRange slots (toF (.neq .idx (lenE input)))

/-- `Witness.accmGen`: no steps needed, `[len < i]`. -/
def accmOut (input : Var Input Fp) : VExpr Fp slots :=
  .mapRange slots (toF (.lt (lenE input) .idx))

/-! ### The output slots -/

/-- The number of positions whose signal `off` selects claim `k`. -/
def countE (off k : ℕ) : FE :=
  (List.range bufferLen).foldr
    (fun i acc => .add (toF (.neq (sigl i off) (cst k))) acc) (.const 0)

/-- `Model.presentCount` -/
def presentE (k : ℕ) : FE := countE sMATCHOUT k
/-- `Model.slotLen` -/
def slotLenE (k : ℕ) : FE := countE sVEMITC k
/-- `Model.signCount` -/
def signE (k : ℕ) : FE := countE sMINUSC k
/-- `Model.trueCount` -/
def trueE (k : ℕ) : FE := countE sTRUEC k

/-- `Model.cell`: the value routed to the flat cell index `c`, from the FIRST
position that routes there (`Model.cell` is a `List.find?`, never a sum). -/
def cellE (c : ℕ) : FE :=
  (List.range bufferLen).foldr
    (fun i acc => .ite (.neq (sigl i sCELLIDX) (cst c)) (.ofU64 (sigl i sVALOUT)) acc)
    (.const 0)

/-- The flat cell index of cell `t` of claim `k`. -/
def cellCode (k t : ℕ) : ℕ := k * ofsMax + t

/-- `Witness.strSlotGen` -/
def strSlotE (k n : ℕ) : StrSlot n FE :=
  { present := presentE k, len := slotLenE k,
    bytes := Vector.ofFn fun t => cellE (cellCode k t.val) }

/-- `Witness.intSlotGen` -/
def intSlotE (k n : ℕ) : IntSlot n FE :=
  { present := presentE k, negative := signE k, len := slotLenE k,
    digits := Vector.ofFn fun t => cellE (cellCode k t.val) }

/-- `Witness.boolSlotGen` -/
def boolSlotE (k : ℕ) : BoolSlot FE := { present := presentE k, value := trueE k }

/-- `Witness.outputGen` -/
def outStruct : Output FE :=
  { iss := strSlotE 0 _, sub := strSlotE 1 _, aud := strSlotE 2 _, azp := strSlotE 3 _,
    hd := strSlotE 4 _, email := strSlotE 5 _, emailVerified := boolSlotE 6,
    nonce := strSlotE 7 _, atHash := strSlotE 8 _, iat := intSlotE 9 _, exp := intSlotE 10 _ }

/-- The output as a vector output expression. -/
def outLit : VExpr Fp (ProvableType.size Output) := .lit (ProvableType.toElements outStruct)

/-! ## The eleven witness programs -/

/-- `Witness.stGen` as an IR program. -/
def stIR (input : Var Input Fp) : WitgenIR Fp (nSt * slots) := .ir (runSteps input) stOut
/-- `Witness.subGen` as an IR program. -/
def subIR (input : Var Input Fp) : WitgenIR Fp (nSub * slots) := .ir (runSteps input) subOut
/-- `Witness.mGen` as an IR program. -/
def mIR (input : Var Input Fp) : WitgenIR Fp (nClaims * slots) := .ir (runSteps input) mOut
/-- `Witness.claimGen` as an IR program. -/
def claimIR (input : Var Input Fp) : WitgenIR Fp (nClaims * slots) :=
  .ir (runSteps input) claimOut
/-- `Witness.hexAccGen` as an IR program. -/
def hexAccIR (input : Var Input Fp) : WitgenIR Fp slots := .ir (runSteps input) hexAccOut
/-- `Witness.kIdxGen` as an IR program. -/
def kIdxIR (input : Var Input Fp) : WitgenIR Fp slots := .ir (runSteps input) kIdxOut
/-- `Witness.ofsGen` as an IR program. -/
def ofsIR (input : Var Input Fp) : WitgenIR Fp slots := .ir (runSteps input) ofsOut
/-- `Witness.nMemGen` as an IR program. -/
def nMemIR (input : Var Input Fp) : WitgenIR Fp slots := .ir (runSteps input) nMemOut
/-- `Witness.lenFlagsGen` as an IR program. -/
def lenFlagsIR (input : Var Input Fp) : WitgenIR Fp slots := .ir [] (lenFlagsOut input)
/-- `Witness.accmGen` as an IR program. -/
def accmIR (input : Var Input Fp) : WitgenIR Fp slots := .ir [] (accmOut input)
/-- `Witness.outputGen` as an IR program. -/
def outIR (input : Var Input Fp) : WitgenIR Fp (ProvableType.size Output) :=
  .ir (runSteps input) outLit

/-! ## Bridging the program back to `Witness.lean`

The witness program is only supposed to agree with the nat model of `Model.lean` on
*honest* inputs: `U64Expr.val` truncates `ZMod.val` to 64 bits, so the bridges below
carry the two hypotheses of `ProverAssumptions` that rule the truncation out (the buffer
holds bytes, the length is at most `bufferLen`). They are what `Main.completeness` needs;
soundness never looks at a witness generator. -/

section Bridge

set_option maxRecDepth 20000

open Witgen (Ctx evalSteps)

/-- The honest run of the nat model over the input under a prover environment. -/
abbrev runOf (input : Var Input Fp) (env : ProverEnvironment Fp) (i : ℕ) : Model.Regs :=
  Model.run (Witness.bytesOf input env) (Witness.lenOf input env) i

/-! ### `letU`-chain reasoning

The three standard facts about `Witgen.evalSteps`: it is a left fold, every step
contributes exactly one local, and appending steps never disturbs an earlier one. -/

/-- Evaluating a concatenation of step lists is evaluating them in sequence. -/
theorem evalSteps_append (env : ProverEnvironment Fp) (steps steps' : List (Witgen.Step Fp))
    (locals : Array (Fp ⊕ UInt64)) :
    evalSteps env (steps ++ steps') locals
      = evalSteps env steps' (evalSteps env steps locals) := by
  induction steps generalizing locals with
  | nil => rfl
  | cons st steps ih => cases st <;> simp only [List.cons_append, evalSteps, ih]

/-- Each step contributes exactly one local. -/
theorem size_evalSteps (env : ProverEnvironment Fp) (steps : List (Witgen.Step Fp))
    (locals : Array (Fp ⊕ UInt64)) :
    (evalSteps env steps locals).size = locals.size + steps.length := by
  induction steps generalizing locals with
  | nil => simp [evalSteps]
  | cons st steps ih =>
      cases st <;> simp only [evalSteps, ih, List.length_cons, Array.size_push] <;> omega

/-- Appending steps never disturbs an already-bound local. -/
theorem getElem?_evalSteps (env : ProverEnvironment Fp) (steps : List (Witgen.Step Fp))
    (locals : Array (Fp ⊕ UInt64)) {i : ℕ} (hi : i < locals.size) :
    (evalSteps env steps locals)[i]? = locals[i]? := by
  induction steps generalizing locals with
  | nil => rfl
  | cons st steps ih =>
      cases st <;>
        simp only [evalSteps] <;>
        rw [ih _ (by rw [Array.size_push]; omega), Array.getElem?_push,
          if_neg (by omega : ¬ i = locals.size)]

/-! ### The block layout -/

theorem length_initBlock : initBlock.length = nRegs := by
  simp [initBlock, nRegs, rM]; omega

theorem length_stepBlock (input : Var Input Fp) (i : ℕ) :
    (stepBlock input i).length = blockSize := by
  simp [stepBlock, blockSize, nSigs, nRegs, rM, nClaims]

/-- The steps of the run, split at position `i`. -/
theorem stepsUpTo_succ (input : Var Input Fp) (i : ℕ) :
    stepsUpTo input (i + 1) = stepsUpTo input i ++ stepBlock input i := by
  simp only [stepsUpTo, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]

theorem length_stepsUpTo (input : Var Input Fp) (i : ℕ) :
    (stepsUpTo input i).length = nRegs + blockSize * i := by
  induction i with
  | zero => simp [stepsUpTo, length_initBlock]
  | succ i ih => rw [stepsUpTo_succ, List.length_append, ih, length_stepBlock]; ring

/-- Every earlier `stepsUpTo` is a prefix of a later one. -/
theorem stepsUpTo_append (input : Var Input Fp) (i j : ℕ) :
    ∃ rest, stepsUpTo input (i + j) = stepsUpTo input i ++ rest := by
  induction j with
  | zero => exact ⟨[], by simp⟩
  | succ j ih =>
      obtain ⟨rest, hrest⟩ := ih
      exact ⟨rest ++ stepBlock input (i + j), by
        rw [show i + (j + 1) = (i + j) + 1 from rfl, stepsUpTo_succ, hrest, List.append_assoc]⟩

/-- `stepsUpTo` is a prefix of the whole program. -/
theorem stepsUpTo_prefix (input : Var Input Fp) {i : ℕ} (hi : i ≤ bufferLen) :
    ∃ rest, runSteps input = stepsUpTo input i ++ rest := by
  have : i + (bufferLen - i) = bufferLen := by omega
  simpa [runSteps, this] using stepsUpTo_append input i (bufferLen - i)

/-- The locals of a prefix are the locals of the whole program. -/
theorem getElem?_runSteps_of_lt (input : Var Input Fp) (env : ProverEnvironment Fp)
    {i j : ℕ} (hi : i ≤ bufferLen) (hj : j < nRegs + blockSize * i) :
    (evalSteps env (runSteps input))[j]? = (evalSteps env (stepsUpTo input i))[j]? := by
  obtain ⟨rest, hrest⟩ := stepsUpTo_prefix input hi
  rw [hrest, evalSteps_append]
  exact getElem?_evalSteps _ _ _ (by rw [size_evalSteps]; simpa [length_stepsUpTo] using hj)

/-! ### The register block

`HoldsRegs L i r` says that the locals `L` encode the registers `r` at block `i`,
in the encoding of the file header. -/

/-- The u64 encoding of the claim register (`claimNone` for `none`). -/
def claimCode (c : Option Model.Claim) : ℕ := c.elim claimNone Fin.val

/-- The locals `L` hold the register block of `r` at block index `i`. -/
def HoldsRegs (L : Array (Fp ⊕ UInt64)) (i : ℕ) (r : Model.Regs) : Prop :=
  L[regBase i + rST]? = some (.inr (UInt64.ofNat r.st.val)) ∧
  L[regBase i + rSUB]? = some (.inr (UInt64.ofNat r.sub.val)) ∧
  L[regBase i + rHEXACC]? = some (.inr (UInt64.ofNat r.hexAcc)) ∧
  L[regBase i + rKIDX]? = some (.inr (UInt64.ofNat r.kIdx)) ∧
  L[regBase i + rCLAIM]? = some (.inr (UInt64.ofNat (claimCode r.claim))) ∧
  L[regBase i + rOFS]? = some (.inr (UInt64.ofNat r.ofs)) ∧
  L[regBase i + rNMEM]? = some (.inr (UInt64.ofNat r.nMem)) ∧
  ∀ k : Model.Claim, L[regBase i + (rM + k.val)]? = some (.inr (if r.m[k] then 1 else 0))

/-! ### Register bounds

Every register of the honest run stays far below `2 ^ 64`, so the u64 encoding never
wraps. `st` and `sub` are `Fin`s; the rest needs an induction over the run. -/

/-- `if c then none else some x = some y` forces `y = x`. -/
private theorem ite_none_some {α : Type} (c : Prop) [Decidable c] (x y : α)
    (h : (if c then none else some x) = some y) : y = x := by
  split at h
  · exact absurd h (by simp)
  · exact (Option.some.inj h).symm

/-- What one step of the model does to the three saturating registers. -/
theorem step_bounds {r r' : Model.Regs} {b : ℕ} (h : Model.step r b = some r') :
    r'.kIdx ≤ kIdxMax - 1 ∧ r'.ofs ≤ ofsMax - 1 ∧ r'.nMem ≤ r.nMem + 1 := by
  simp only [Model.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨sub', -, st', -, h⟩ := h
  rw [ite_none_some _ _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · dsimp only
    split
    · exact Nat.min_le_right _ _
    · omega
  · exact Nat.min_le_right _ _
  · dsimp only; split <;> omega

/-- The step of the run, unfolded. -/
theorem run_succ (bytes : ℕ → ℕ) (len i : ℕ) :
    Model.run bytes len (i + 1)
      = if i < len then (Model.step (Model.run bytes len i) (bytes i)).getD (Model.run bytes len i)
        else Model.run bytes len i := rfl

/-- `kIdx` saturates at `kIdxMax - 1`. -/
theorem run_kIdx_le (bytes : ℕ → ℕ) (len i : ℕ) :
    (Model.run bytes len i).kIdx ≤ kIdxMax - 1 := by
  induction i with
  | zero => simp [Model.run, Model.Regs.init]
  | succ i ih =>
      rw [run_succ]
      split
      · cases hs : Model.step (Model.run bytes len i) (bytes i) with
        | none => simpa using ih
        | some r' => simpa using (step_bounds hs).1
      · exact ih

/-- `ofs` saturates at `ofsMax - 1`. -/
theorem run_ofs_le (bytes : ℕ → ℕ) (len i : ℕ) :
    (Model.run bytes len i).ofs ≤ ofsMax - 1 := by
  induction i with
  | zero => simp [Model.run, Model.Regs.init]
  | succ i ih =>
      rw [run_succ]
      split
      · cases hs : Model.step (Model.run bytes len i) (bytes i) with
        | none => simpa using ih
        | some r' => simpa using (step_bounds hs).2.1
      · exact ih

/-- `nMem` counts key starts, at most one per position. -/
theorem run_nMem_le (bytes : ℕ → ℕ) (len i : ℕ) : (Model.run bytes len i).nMem ≤ i := by
  induction i with
  | zero => simp [Model.run, Model.Regs.init]
  | succ i ih =>
      rw [run_succ]
      split
      · cases hs : Model.step (Model.run bytes len i) (bytes i) with
        | none => simp only [Option.getD]; omega
        | some r' =>
            simp only [Option.getD]
            exact le_trans (step_bounds hs).2.2 (Nat.succ_le_succ ih)
      · omega

/-- A hex digit's value is a hex digit. -/
theorem hexVal_lt (b : ℕ) : Model.hexVal b < 16 := by
  unfold Model.hexVal Model.isDigit Model.isUpperHex Model.isLowerHex
  simp only [Specs.JSON.digit0, Specs.JSON.digit9, Specs.JSON.upperA, Specs.JSON.upperF,
    Specs.JSON.lowerA, Specs.JSON.lowerF, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs with h1 h2 h3 <;> omega

theorem signals_hexVal (r : Model.Regs) (b : ℕ) (st' : Model.St) :
    (Model.signals r b st').hexVal = Model.hexVal b := rfl

/-- The bound `hexAcc` obeys in each sub state: the `\uXXXX` states `H1 → H2 → H3` each
admit one more hex digit. -/
def hexBound (s : Model.Sub) : ℕ :=
  if s = Model.Sub.H1 then 1 else if s = Model.Sub.H2 then 16
  else if s = Model.Sub.H3 then 256 else 4096

theorem hexBound_pos (s : Model.Sub) : 0 < hexBound s := by
  unfold hexBound; split_ifs <;> omega

theorem hexBound_le (s : Model.Sub) : hexBound s ≤ 4096 := by
  unfold hexBound; split_ifs <;> omega

/-- From `H1` the sub automaton goes to `H2` (or leaves the string). -/
theorem stepSub_of_H1 {inStr : Bool} {b : ℕ} {s' : Model.Sub}
    (h : Model.stepSub inStr Model.Sub.H1 b = some s') : 16 ≤ hexBound s' := by
  cases inStr with
  | false =>
      rw [show Model.stepSub false Model.Sub.H1 b = some Model.Sub.PLAIN from rfl] at h
      rw [← Option.some.inj h]; decide
  | true =>
      rw [show Model.stepSub true Model.Sub.H1 b
        = if Model.isHex b then some Model.Sub.H2 else none from rfl] at h
      split at h
      · rw [← Option.some.inj h]; decide
      · exact absurd h (by simp)

/-- From `H2` the sub automaton goes to `H3` (or leaves the string). -/
theorem stepSub_of_H2 {inStr : Bool} {b : ℕ} {s' : Model.Sub}
    (h : Model.stepSub inStr Model.Sub.H2 b = some s') : 256 ≤ hexBound s' := by
  cases inStr with
  | false =>
      rw [show Model.stepSub false Model.Sub.H2 b = some Model.Sub.PLAIN from rfl] at h
      rw [← Option.some.inj h]; decide
  | true =>
      rw [show Model.stepSub true Model.Sub.H2 b
        = if Model.isHex b then some Model.Sub.H3 else none from rfl] at h
      split at h
      · rw [← Option.some.inj h]; decide
      · exact absurd h (by simp)

/-- From `H3` the sub automaton goes to `H4` (or leaves the string). -/
theorem stepSub_of_H3 {inStr : Bool} {b : ℕ} {s' : Model.Sub}
    (h : Model.stepSub inStr Model.Sub.H3 b = some s') : 4096 ≤ hexBound s' := by
  cases inStr with
  | false =>
      rw [show Model.stepSub false Model.Sub.H3 b = some Model.Sub.PLAIN from rfl] at h
      rw [← Option.some.inj h]; decide
  | true =>
      rw [show Model.stepSub true Model.Sub.H3 b
        = if Model.isHex b then some Model.Sub.H4 else none from rfl] at h
      split at h
      · rw [← Option.some.inj h]; decide
      · exact absurd h (by simp)

/-- The `hexAcc` invariant: `sub` records how many hex digits have been accumulated. -/
def HexInv (r : Model.Regs) : Prop := r.hexAcc < hexBound r.sub

theorem step_hexInv {r r' : Model.Regs} {b : ℕ} (hinv : HexInv r)
    (h : Model.step r b = some r') : HexInv r' := by
  have hinv' : r.hexAcc < hexBound r.sub := hinv
  simp only [Model.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨sub', hsub, st', -, h⟩ := h
  have hv := hexVal_lt b
  have hb := hexBound_pos sub'
  rw [ite_none_some _ _ _ h]
  clear h hinv
  show (if _ then _ else _) < hexBound sub'
  simp only [signals_hexVal, Bool.or_eq_true, decide_eq_true_eq]
  split
  · rename_i hcase
    rcases hcase with (hc | hc) | hc
    · have hs := stepSub_of_H1 (hc ▸ hsub)
      rw [hc] at hinv'
      simp [hexBound] at hinv'
      exact lt_of_lt_of_le (by simp [hinv']; omega) hs
    · have hs := stepSub_of_H2 (hc ▸ hsub)
      rw [hc] at hinv'
      norm_num [hexBound, Model.Sub.H1, Model.Sub.H2, Model.nSub, Fin.ext_iff] at hinv'
      refine lt_of_lt_of_le ?_ hs
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.mul_le_mul (le_refl 16) (by omega : r.hexAcc ≤ 15))
          (by omega : Model.hexVal b ≤ 15)) (by norm_num)
    · have hs := stepSub_of_H3 (hc ▸ hsub)
      rw [hc] at hinv'
      norm_num [hexBound, Model.Sub.H1, Model.Sub.H2, Model.Sub.H3, Model.nSub,
        Fin.ext_iff] at hinv'
      refine lt_of_lt_of_le ?_ hs
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.mul_le_mul (le_refl 16) (by omega : r.hexAcc ≤ 255))
          (by omega : Model.hexVal b ≤ 15)) (by norm_num)
  · omega

theorem run_hexInv (bytes : ℕ → ℕ) (len i : ℕ) : HexInv (Model.run bytes len i) := by
  induction i with
  | zero =>
      show (0 : ℕ) < hexBound Model.Sub.PLAIN
      norm_num [hexBound, Model.Sub.PLAIN, Model.Sub.H1, Model.Sub.H2, Model.Sub.H3,
        Fin.ext_iff]
  | succ i ih =>
      rw [run_succ]
      split
      · cases hs : Model.step (Model.run bytes len i) (bytes i) with
        | none => simpa using ih
        | some r' => simpa using step_hexInv ih hs
      · exact ih

/-- `hexAcc` accumulates at most three hex digits (`sub` walks `H1 → H2 → H3 → H4`). -/
theorem run_hexAcc_lt (bytes : ℕ → ℕ) (len i : ℕ) :
    (Model.run bytes len i).hexAcc < 4096 :=
  lt_of_lt_of_le (run_hexInv bytes len i) (hexBound_le _)

/-! ### Scalar helpers -/

private theorem lt64_of_le_bufferLen {n : ℕ} (h : n ≤ bufferLen) : n < 2 ^ 64 := by
  simp only [bufferLen] at h; omega

/-- The `FiniteField` embedding of the instance's field is `ZMod.val`. -/
private theorem ff_val (x : Fp) : FiniteField.val x = ZMod.val x := rfl

private theorem nSt_lt64 : nSt < 2 ^ 64 := by norm_num [Model.nSt]
private theorem nSub_lt64 : nSub < 2 ^ 64 := by norm_num [Model.nSub]
private theorem nClaims_succ_lt64 : nClaims + 1 < 2 ^ 64 := by norm_num [Model.nClaims]

theorem ofNat_inj {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (UInt64.ofNat a = UInt64.ofNat b) ↔ a = b := by
  rw [← UInt64.toNat_inj, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_lt_ofNat {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (UInt64.ofNat a < UInt64.ofNat b) ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem fromNat_ofNat {n : ℕ} (hn : n < 2 ^ 64) :
    (FiniteField.fromNat (UInt64.ofNat n).toNat : Fp) = (n : Fp) := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]; rfl

/-- The claim register encoding decides `Model.Regs.claim`. -/
theorem claimCode_eq_iff {c : Option Model.Claim} {j : ℕ} (hj : j < nClaims) :
    claimCode c = j ↔ c = some ⟨j, hj⟩ := by
  cases c with
  | none => simp only [claimCode, claimNone, Option.elim, reduceCtorEq, iff_false]; omega
  | some k => simp [claimCode, Fin.ext_iff]


/-! ### Reading u64-sorted expressions as naturals

Every local of the program is a small natural number, so its u64 arithmetic never wraps.
`UIs ctx x v` says the u64-sorted expression `x` evaluates to the natural number `v`; the
lemmas below propagate that through the combinators the program is built from, so the
per-signal lemmas of the layout theorem can be stated and chained in `ℕ` instead of in
`UInt64`. -/

/-- `UInt64.ofNat` is additive (both sides wrap the same way). -/
private theorem ofNat_add (v w : ℕ) :
    UInt64.ofNat v + UInt64.ofNat w = UInt64.ofNat (v + w) := by
  rw [← UInt64.toNat_inj, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    UInt64.toNat_ofNat']
  omega

/-- `UInt64.ofNat` is multiplicative. -/
private theorem ofNat_mul (v w : ℕ) :
    UInt64.ofNat v * UInt64.ofNat w = UInt64.ofNat (v * w) := by
  rw [← UInt64.toNat_inj, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    UInt64.toNat_ofNat']
  simp [Nat.mul_mod]

/-- The u64-sorted expression `x` evaluates to the natural number `v`, which fits a u64. -/
def UIs (ctx : Witgen.Ctx Fp) (x : UE) (v : ℕ) : Prop :=
  v < 2 ^ 64 ∧ Witgen.U64Expr.eval ctx x = UInt64.ofNat v

namespace UIs

variable {ctx : Witgen.Ctx Fp} {x y : UE} {v w : ℕ}

theorem bound (h : UIs ctx x v) : v < 2 ^ 64 := h.1
theorem eval (h : UIs ctx x v) : Witgen.U64Expr.eval ctx x = UInt64.ofNat v := h.2

theorem cst {n : ℕ} (hn : n < 2 ^ 64) : UIs ctx (IR.cst n) n := ⟨hn, rfl⟩

theorem localVar {j : ℕ} (hv : v < 2 ^ 64)
    (h : ctx.locals[j]? = some (.inr (UInt64.ofNat v))) : UIs ctx (.localVar j) v :=
  ⟨hv, by simp only [Witgen.U64Expr.eval, h]⟩

theorem congr (h : UIs ctx x v) (hvw : v = w) : UIs ctx x w := hvw ▸ h

theorem ite {c : BE} (hx : UIs ctx x v) (hy : UIs ctx y w) :
    UIs ctx (.ite c x y) (if Witgen.BExpr.eval ctx c then v else w) := by
  refine ⟨?_, ?_⟩ <;> rcases hc : Witgen.BExpr.eval ctx c with _ | _ <;>
    simp only [UIs, Witgen.U64Expr.eval, hc, if_true, if_false, Bool.false_eq_true,
      hx.1, hx.2, hy.1, hy.2]

theorem add (hx : UIs ctx x v) (hy : UIs ctx y w) (h : v + w < 2 ^ 64) :
    UIs ctx (.add x y) (v + w) :=
  ⟨h, by simp only [Witgen.U64Expr.eval, hx.2, hy.2, ofNat_add]⟩

theorem mul (hx : UIs ctx x v) (hy : UIs ctx y w) (h : v * w < 2 ^ 64) :
    UIs ctx (.mul x y) (v * w) :=
  ⟨h, by simp only [Witgen.U64Expr.eval, hx.2, hy.2, ofNat_mul]⟩

/-- The wrapping subtraction of `IR.subN` is exact below the operand. -/
theorem subN (hx : UIs ctx x v) {n : ℕ} (hn : n ≤ v) : UIs ctx (IR.subN x n) (v - n) := by
  have hv := hx.1
  refine ⟨by omega, ?_⟩
  simp only [IR.subN, Witgen.U64Expr.eval, hx.2, ofNat_add]
  rw [← UInt64.toNat_inj, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  have h1 : v + (2 ^ 64 - n) = (v - n) + 2 ^ 64 := by omega
  rw [h1, Nat.add_mod_right]

theorem minN (hx : UIs ctx x v) {n : ℕ} (hn : n < 2 ^ 64) :
    UIs ctx (IR.minN x n) (min v n) := by
  have hv := hx.1
  refine ⟨by omega, ?_⟩
  simp only [IR.minN, Witgen.U64Expr.eval, Witgen.BExpr.eval, hx.2, IR.cst,
    UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hv]
  by_cases h : n < v
  · rw [if_pos (by simpa using h), Nat.min_eq_right (by omega)]
  · rw [if_neg (by simpa using h), Nat.min_eq_left (by omega)]

/-- A `0`/`1` flag. -/
theorem toU {c : BE} :
    UIs ctx (IR.toU c) (if Witgen.BExpr.eval ctx c then 1 else 0) :=
  UIs.ite (UIs.cst (n := 1) (by norm_num)) (UIs.cst (n := 0) (by norm_num))

/-- The field value of an embedded circuit expression, below `2 ^ 64`. -/
theorem valExpr {e : Expression Fp} (hv : v < 2 ^ 64)
    (h : FiniteField.val (Expression.eval ctx.env.toEnvironment e) = v) :
    UIs ctx (.val (.expr e)) v :=
  ⟨hv, by simp only [Witgen.U64Expr.eval, Witgen.FExpr.eval, h]⟩

end UIs

/-! Conditions, read back as decidable `ℕ` statements. -/

theorem eval_bor (ctx : Witgen.Ctx Fp) (p q : BE) :
    Witgen.BExpr.eval ctx (bor p q) = (Witgen.BExpr.eval ctx p || Witgen.BExpr.eval ctx q) := by
  simp only [bor, Witgen.BExpr.eval, Bool.not_and, Bool.not_not]

theorem eval_and (ctx : Witgen.Ctx Fp) (p q : BE) :
    Witgen.BExpr.eval ctx (.and p q)
      = (Witgen.BExpr.eval ctx p && Witgen.BExpr.eval ctx q) := rfl

theorem eval_not (ctx : Witgen.Ctx Fp) (p : BE) :
    Witgen.BExpr.eval ctx (.not p) = !Witgen.BExpr.eval ctx p := rfl

theorem eval_neqU {ctx : Witgen.Ctx Fp} {x y : UE} {v w : ℕ} (hx : UIs ctx x v)
    (hy : UIs ctx y w) : Witgen.BExpr.eval ctx (.neq x y) = decide (v = w) := by
  simp only [Witgen.BExpr.eval, hx.2, hy.2, decide_eq_decide]
  exact ofNat_inj hx.1 hy.1

theorem eval_eqn {ctx : Witgen.Ctx Fp} {x : UE} {v : ℕ} (hx : UIs ctx x v) {n : ℕ}
    (hn : n < 2 ^ 64) : Witgen.BExpr.eval ctx (eqn x n) = decide (v = n) := by
  simp only [eqn, Witgen.BExpr.eval, hx.2, cst, decide_eq_decide]
  exact ofNat_inj hx.1 hn

theorem eval_ltU {ctx : Witgen.Ctx Fp} {x y : UE} {v w : ℕ} (hx : UIs ctx x v)
    (hy : UIs ctx y w) : Witgen.BExpr.eval ctx (.lt x y) = decide (v < w) := by
  simp only [Witgen.BExpr.eval, hx.2, hy.2, decide_eq_decide]
  exact ofNat_lt_ofNat hx.1 hy.1

theorem eval_leN {ctx : Witgen.Ctx Fp} {x : UE} {v : ℕ} (hx : UIs ctx x v) {n : ℕ}
    (hn : n < 2 ^ 64) : Witgen.BExpr.eval ctx (leN x n) = decide (v ≤ n) := by
  rw [leN, show Witgen.BExpr.eval ctx (.not (.lt (cst n) x))
      = !Witgen.BExpr.eval ctx (.lt (cst n) x) from rfl,
    eval_ltU (UIs.cst hn) hx]
  rcases Nat.lt_or_ge n v with h | h
  · simp [h, Nat.not_le.mpr h]
  · simp [Nat.not_lt.mpr h, h]

theorem eval_geN {ctx : Witgen.Ctx Fp} {x : UE} {v : ℕ} (hx : UIs ctx x v) {n : ℕ}
    (hn : n < 2 ^ 64) : Witgen.BExpr.eval ctx (geN x n) = decide (n ≤ v) := by
  rw [geN, show Witgen.BExpr.eval ctx (.not (.lt x (cst n)))
      = !Witgen.BExpr.eval ctx (.lt x (cst n)) from rfl,
    eval_ltU hx (UIs.cst hn)]
  rcases Nat.lt_or_ge v n with h | h
  · simp [h, Nat.not_le.mpr h]
  · simp [Nat.not_lt.mpr h, h]

theorem eval_rngN {ctx : Witgen.Ctx Fp} {x : UE} {v : ℕ} (hx : UIs ctx x v) {lo hi : ℕ}
    (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64) :
    Witgen.BExpr.eval ctx (rngN x lo hi) = (decide (lo ≤ v) && decide (v ≤ hi)) := by
  rw [rngN, show Witgen.BExpr.eval ctx (.and (geN x lo) (leN x hi))
      = (Witgen.BExpr.eval ctx (geN x lo) && Witgen.BExpr.eval ctx (leN x hi)) from rfl,
    eval_geN hx hlo, eval_leN hx hhi]

theorem eval_anyEq {ctx : Witgen.Ctx Fp} {x : UE} {v : ℕ} (hx : UIs ctx x v) :
    ∀ ns : List ℕ, (∀ n ∈ ns, n < 2 ^ 64) →
      Witgen.BExpr.eval ctx (anyEq x ns) = ns.any (fun n => decide (v = n))
  | [], _ => by simp [anyEq, Witgen.BExpr.eval]
  | [n], h => by
      simp only [anyEq, eval_eqn hx (h n (by simp)), List.any_cons, List.any_nil, Bool.or_false]
  | n :: m :: ns, h => by
      have hrec : Witgen.BExpr.eval ctx (anyEq x (m :: ns))
          = (m :: ns).any (fun k => decide (v = k)) :=
        eval_anyEq hx (m :: ns) (fun k hk => h k (by simp [hk]))
      simp only [anyEq, eval_bor, eval_eqn hx (h n (by simp)), hrec, List.any_cons]

/-! ### The model side of a block

`Model.signals` takes the successor main state as a parameter, but only `keyStart` reads
it; the program computes that state in its own `stepSt` local, so the model function the
program mirrors is `sigOf`, which plugs in the same successor (`r.st` on a rejection).
Every other field of `Model.signals` ignores the argument, so `sigOf` agrees with
`Model.runSignals` on everything the output read-outs look at. -/

/-- A flag as the natural number the program stores. -/
def ub (c : Bool) : ℕ := if c then 1 else 0

@[simp] theorem ub_lt (c : Bool) : ub c < 2 ^ 64 := by cases c <;> simp [ub]

@[simp] theorem ub_le_one (c : Bool) : ub c ≤ 1 := by cases c <;> simp [ub]

@[simp] theorem ub_eq_one (c : Bool) : (ub c = 1) = (c = true) := by cases c <;> simp [ub]

/-- The u64 code of an optional main state (`stNone` for a rejection). -/
def stCode (s : Option Model.St) : ℕ := s.elim stNone Fin.val

/-- The u64 code of an optional sub state (`subNone` for a rejection). -/
def subCode (s : Option Model.Sub) : ℕ := s.elim subNone Fin.val

/-- The successor sub state of the model, as the program's code. -/
def subnOf (r : Model.Regs) (b : ℕ) : ℕ := subCode (Model.stepSub (Model.inStr r.st) r.sub b)

/-- The successor main state of the model, as the program's code. -/
def stnOf (r : Model.Regs) (b : ℕ) : ℕ :=
  stCode (Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Model.Sub.PLAIN)) r.st b)

/-- The signals of the model at a position, with the program's successor main state. -/
def sigOf (r : Model.Regs) (b : ℕ) : Model.Signals :=
  Model.signals r b
    ((Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Model.Sub.PLAIN)) r.st b).getD r.st)

/-- `Model.kindOf` as the code the program uses (`3` for an unknown claim). -/
def kindOfCode (c : Option Model.Claim) : ℕ := c.elim 3 kindCode

/-- The claim the closing key matches, `claimNone` if none. -/
def matchIdxOf (r : Model.Regs) (b : ℕ) : ℕ :=
  claimCode ((List.finRange nClaims).find? fun k => (sigOf r b).match_[k])

/-- The registers after a position: the model's step when the position is active and the
byte has a transition, the previous registers otherwise. -/
def nextRegs (r : Model.Regs) (b : ℕ) (active : Bool) : Model.Regs :=
  if active then (Model.step r b).getD r else r

/-- The value of local `m` of the block of a position with registers `r` before it, byte
`b` and activity `active`. Locals `0 .. nSigs-1` are the signals, `nSigs .. blockSize-1`
the registers of the next block. -/
def blockVal (r : Model.Regs) (b : ℕ) (active : Bool) : ℕ → ℕ
  | 0 => ub active
  | 1 => b
  | 2 => ub (Model.isWs b)
  | 3 => ub (Model.isDigit b)
  | 4 => ub (Model.isDigitNz b)
  | 5 => ub (Model.isHex b)
  | 6 => ub (Model.isUnescaped b)
  | 7 => ub (Model.isExpLetter b)
  | 8 => ub (Model.isSign b)
  | 9 => ub (Model.isSimpleEsc b)
  | 10 => ub (Model.isCont b)
  | 11 => ub (Model.isLead2 b)
  | 12 => ub (Model.isLead3 b)
  | 13 => ub (Model.isLead4 b)
  | 14 => ub (Model.isContA0BF b)
  | 15 => ub (Model.isCont809F b)
  | 16 => ub (Model.isCont90BF b)
  | 17 => ub (Model.isCont808F b)
  | 18 => ub (Model.inStr r.st)
  | 19 => ub (Model.inStr r.st && r.sub = Model.Sub.PLAIN && Model.isUnescaped b)
  | 20 => ub (Model.inStr r.st && r.sub = Model.Sub.ESC && Model.isSimpleEsc b)
  | 21 => ub (Model.inStr r.st && r.sub = Model.Sub.H4 && Model.isHex b)
  | 22 => ub (Model.inStr r.st && r.sub = Model.Sub.C1 && Model.isCont b)
  | 23 => ub (sigOf r b).emit
  | 24 => Model.hexVal b
  | 25 => (sigOf r b).cp
  | 26 => subnOf r b
  | 27 => kindOfCode r.claim
  | 28 => stCode (Model.afterValue b)
  | 29 => stnOf r b
  | 30 => ub (sigOf r b).keyStart
  | 31 => ub (sigOf r b).keyClose
  | 32 => matchIdxOf r b
  | 33 => ub ((sigOf r b).emit && r.st = Model.St.STR)
  | 34 => ub (sigOf r b).digitEmit
  | 35 => ub (sigOf r b).vEmit
  | 36 => ub (sigOf r b).write
  | 37 => (sigOf r b).valOut
  | 38 => ub (sigOf r b).minusFlag
  | 39 => ub (sigOf r b).trueDone
  | 40 => ub (Model.step r b).isSome
  | 41 => ub (active && (Model.step r b).isSome)
  | 42 => if active && (sigOf r b).write then claimCode r.claim * ofsMax + r.ofs else cellNone
  | 43 => if active then matchIdxOf r b else claimNone
  | 44 => if active && (sigOf r b).vEmit then claimCode r.claim else claimNone
  | 45 => if active && (sigOf r b).minusFlag then claimCode r.claim else claimNone
  | 46 => if active && (sigOf r b).trueDone then claimCode r.claim else claimNone
  | 47 => (nextRegs r b active).st.val
  | 48 => (nextRegs r b active).sub.val
  | 49 => (nextRegs r b active).hexAcc
  | 50 => (nextRegs r b active).kIdx
  | 51 => claimCode (nextRegs r b active).claim
  | 52 => (nextRegs r b active).ofs
  | 53 => (nextRegs r b active).nMem
  | k + 54 => if h : k < nClaims then ub ((nextRegs r b active).m[k]'h) else 0

/-! ### Evaluating one position's block

The locals array is kept in the shape `L ++ accOf V k`: `L` is everything bound before the
block (opaque, known only through `HoldsRegs`) and `accOf V k` are the `k` values bound
inside the block so far. Keeping the two apart is what stops each step's evaluation
context from being nested inside the next step's, which would make the term for the block
grow exponentially. -/

/-- The first `k` locals of a block, as an array of u64-sorted values. -/
def accOf (V : ℕ → ℕ) (k : ℕ) : Array (Fp ⊕ UInt64) :=
  ((List.range k).map (fun m => (Sum.inr (UInt64.ofNat (V m)) : Fp ⊕ UInt64))).toArray

@[simp] theorem size_accOf (V : ℕ → ℕ) (k : ℕ) : (accOf V k).size = k := by simp [accOf]

theorem getElem?_accOf (V : ℕ → ℕ) {k m : ℕ} (h : m < k) :
    (accOf V k)[m]? = some (.inr (UInt64.ofNat (V m))) := by
  simp only [accOf, List.getElem?_toArray, List.getElem?_map, List.getElem?_range h,
    Option.map_some]

theorem accOf_push (V : ℕ → ℕ) (k : ℕ) :
    (accOf V k).push (.inr (UInt64.ofNat (V k))) = accOf V (k + 1) := by
  simp only [accOf, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.push_toArray]

theorem getElem?_append_add (L acc : Array (Fp ⊕ UInt64)) (m : ℕ) :
    (L ++ acc)[L.size + m]? = acc[m]? := by
  rw [Array.getElem?_append_right (by omega)]
  congr 1
  omega

theorem evalSteps_letU_append (env : ProverEnvironment Fp) (L acc : Array (Fp ⊕ UInt64))
    (e : UE) (rest : List (Witgen.Step Fp)) :
    evalSteps env (.letU e :: rest) (L ++ acc)
      = evalSteps env rest
          (L ++ acc.push (.inr (Witgen.U64Expr.eval { env := env, locals := L ++ acc } e))) := by
  simp only [evalSteps, Array.append_push]

/-- The evaluation context at the `k`-th step of a block. -/
def blockCtx (env : ProverEnvironment Fp) (L : Array (Fp ⊕ UInt64)) (V : ℕ → ℕ) (k : ℕ) :
    Witgen.Ctx Fp := { env := env, locals := L ++ accOf V k }

/-- One step of a block, once the value it binds is known. -/
theorem step_accOf {env : ProverEnvironment Fp} {L : Array (Fp ⊕ UInt64)} {V : ℕ → ℕ}
    {k : ℕ} {e : UE} (rest : List (Witgen.Step Fp))
    (hv : UIs (blockCtx env L V k) e (V k)) :
    evalSteps env (.letU e :: rest) (L ++ accOf V k)
      = evalSteps env rest (L ++ accOf V (k + 1)) := by
  rw [evalSteps_letU_append, show Witgen.U64Expr.eval { env := env, locals := L ++ accOf V k } e
    = UInt64.ofNat (V k) from hv.2, accOf_push]

/-- Reading a signal local of the block being evaluated. -/
theorem uis_sigl {env : ProverEnvironment Fp} {L : Array (Fp ⊕ UInt64)} {i : ℕ}
    (hL : L.size = nRegs + blockSize * i) (V : ℕ → ℕ) {k m : ℕ} (hm : m < k)
    (hlt : V m < 2 ^ 64) : UIs (blockCtx env L V k) (sigl i m) (V m) := by
  refine UIs.localVar hlt ?_
  show (L ++ accOf V k)[sigBase i + m]? = _
  have he : sigBase i + m = L.size + m := by simp only [sigBase, hL]; omega
  rw [he, getElem?_append_add, getElem?_accOf V hm]

/-- Reading a register local of the block being evaluated. -/
theorem uis_reg {env : ProverEnvironment Fp} {L : Array (Fp ⊕ UInt64)} {i : ℕ}
    (hL : L.size = nRegs + blockSize * i) (V : ℕ → ℕ) (k : ℕ) {off v : ℕ}
    (hoff : off < nRegs) (hlt : v < 2 ^ 64)
    (h : L[regBase i + off]? = some (.inr (UInt64.ofNat v))) :
    UIs (blockCtx env L V k) (reg i off) v := by
  refine UIs.localVar hlt ?_
  show (L ++ accOf V k)[regBase i + off]? = _
  rw [Array.getElem?_append_left (by simp only [regBase, hL]; omega), h]

/-- A `0`/`1` flag, with the condition already read back. -/
theorem UIs.toU' {ctx : Witgen.Ctx Fp} {c : BE} {d : Bool}
    (h : Witgen.BExpr.eval ctx c = d) : UIs ctx (IR.toU c) (ub d) := h ▸ UIs.toU

/-- A conditional, with the condition already read back. -/
theorem UIs.ite' {ctx : Witgen.Ctx Fp} {c : BE} {x y : UE} {v w : ℕ} {d : Bool}
    (hd : Witgen.BExpr.eval ctx c = d) (hx : UIs ctx x v) (hy : UIs ctx y w) :
    UIs ctx (.ite c x y) (if d then v else w) := hd ▸ UIs.ite hx hy

/-- A conditional whose condition is known to hold. -/
theorem UIs.ite_pos {ctx : Witgen.Ctx Fp} {c : BE} {x y : UE} {v : ℕ}
    (hd : Witgen.BExpr.eval ctx c = true) (hx : UIs ctx x v) : UIs ctx (.ite c x y) v :=
  ⟨hx.1, by simp only [Witgen.U64Expr.eval, hd, if_true, hx.2]⟩

/-- A conditional whose condition is known to fail. -/
theorem UIs.ite_neg {ctx : Witgen.Ctx Fp} {c : BE} {x y : UE} {w : ℕ}
    (hd : Witgen.BExpr.eval ctx c = false) (hy : UIs ctx y w) : UIs ctx (.ite c x y) w :=
  ⟨hy.1, by simp only [Witgen.U64Expr.eval, hd, Bool.false_eq_true, if_false, hy.2]⟩

theorem UIs.chain_nil {ctx : Witgen.Ctx Fp} {dflt : UE} {v : ℕ} (h : UIs ctx dflt v) :
    UIs ctx (chain [] dflt) v := h

theorem UIs.chain_cons {ctx : Witgen.Ctx Fp} {c : BE} {x : UE} {ds : List (BE × UE)}
    {dflt : UE} {d : Bool} {v w : ℕ} (hd : Witgen.BExpr.eval ctx c = d)
    (hx : UIs ctx x v) (hrest : UIs ctx (chain ds dflt) w) :
    UIs ctx (chain ((c, x) :: ds) dflt) (if d then v else w) :=
  UIs.ite' hd hx hrest

/-- A `0`/`1` local, read back as the condition it stands for. -/
theorem eval_flagN {ctx : Witgen.Ctx Fp} {x : UE} {c : Bool} (h : UIs ctx x (ub c)) :
    Witgen.BExpr.eval ctx (eqn x 1) = c := by
  rw [eval_eqn h (by norm_num)]
  cases c <;> simp [ub]

/-! ### The layout theorem

The heart of the bridge: block `i` of the locals is the register encoding of
`Model.run bytes len i`. The induction step is the per-position lemma, a
`split_ifs` over exactly the decision trees of `Model.stepSub` / `Model.stepSt` /
`Model.step` that `stepBlock` mirrors. -/

/-! ### Pushing the state codes through a decision tree -/

theorem subCode_ite (c : Prop) [Decidable c] (x y : Option Model.Sub) :
    subCode (if c then x else y) = if c then subCode x else subCode y := by split <;> rfl

theorem subCode_some (s : Model.Sub) : subCode (some s) = s.val := rfl

theorem subCode_none : subCode (none : Option Model.Sub) = subNone := rfl

theorem stCode_ite (c : Prop) [Decidable c] (x y : Option Model.St) :
    stCode (if c then x else y) = if c then stCode x else stCode y := by split <;> rfl

theorem stCode_some (s : Model.St) : stCode (some s) = s.val := rfl

theorem stCode_none : stCode (none : Option Model.St) = stNone := rfl

/-! ### `Model.step`, decomposed

`Model.step` rejects when either automaton has no transition, when a routed value would
overflow its slot, or when a known string claim gets a non-ASCII code point. The program
tests exactly those four things, on its own sentinel encoding. -/

/-- The slot cap of the claim register (`0` for `none`, where it is unused). -/
def capOf (c : Option Model.Claim) : ℕ := c.elim 0 Model.claimCap

theorem subnOf_eq_subNone_iff (r : Model.Regs) (b : ℕ) :
    (subnOf r b = subNone) ↔ Model.stepSub (Model.inStr r.st) r.sub b = none := by
  cases h : Model.stepSub (Model.inStr r.st) r.sub b with
  | none => simp [subnOf, subCode, h]
  | some s =>
      have hs := s.isLt
      simp only [Model.nSub] at hs
      simp only [subnOf, subCode, h, Option.elim, subNone, Model.nSub, reduceCtorEq, iff_false]
      omega

theorem stnOf_eq_stNone_iff (r : Model.Regs) (b : ℕ) :
    (stnOf r b = stNone) ↔
      Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Model.Sub.PLAIN)) r.st b = none := by
  cases h : Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Model.Sub.PLAIN)) r.st b with
  | none => simp [stnOf, stCode, h]
  | some s =>
      have hs := s.isLt
      simp only [Model.nSt] at hs
      simp only [stnOf, stCode, h, Option.elim, stNone, Model.nSt, reduceCtorEq, iff_false]
      omega

private theorem ite_isSome {α : Type} (c : Bool) (x : α) :
    (if (!c) = true then (none : Option α) else pure x).isSome = c := by
  cases c <;> simp [pure]

/-- The program's rejection test is `Model.step`'s. -/
theorem step_isSome_eq (r : Model.Regs) (b : ℕ) :
    ((!decide (subnOf r b = subNone) && !decide (stnOf r b = stNone)) &&
      ((!(sigOf r b).write ||
          (decide (claimCode r.claim = claimNone) || decide (r.ofs < capOf r.claim))) &&
        (!((sigOf r b).write && decide (r.st = Model.St.STR)) ||
          decide ((sigOf r b).cp < 0x80))))
      = (Model.step r b).isSome := by
  simp only [Model.step, Option.bind_eq_bind]
  cases hsub : Model.stepSub (Model.inStr r.st) r.sub b with
  | none =>
      rw [decide_eq_true ((subnOf_eq_subNone_iff r b).mpr hsub)]
      simp
  | some sub' =>
      cases hst : Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Model.Sub.PLAIN)) r.st b with
      | none =>
          rw [decide_eq_true ((stnOf_eq_stNone_iff r b).mpr hst)]
          simp
      | some st' =>
          have hne1 : ¬ (subnOf r b = subNone) := fun h =>
            by simp [(subnOf_eq_subNone_iff r b).mp h] at hsub
          have hne2 : ¬ (stnOf r b = stNone) := fun h =>
            by simp [(stnOf_eq_stNone_iff r b).mp h] at hst
          have hsig : sigOf r b = Model.signals r b st' := by
            simp only [sigOf, hst, Option.getD]
          rw [decide_eq_false hne1, decide_eq_false hne2, hsig]
          simp only [Option.bind, Bool.not_false, Bool.and_self, Bool.true_and, ite_isSome]
          cases hc : r.claim with
          | none =>
              simp only [claimCode, hc, Option.elim, decide_true, Bool.or_true, Bool.true_or]
          | some k =>
              have hk : ¬ (k.val = claimNone) := by
                have := k.isLt; simp only [Model.nClaims] at this
                simp only [claimNone, Model.nClaims]; omega
              simp only [claimCode, hc, Option.elim, capOf]
              simp [hk]
              rfl

/-! ### Index folds

The program reads a per-claim table by folding a decision chain over `List.finRange
nClaims`; the value is the first claim whose guard holds. -/

theorem uis_foldr_pred {ctx : Witgen.Ctx Fp} {n : ℕ} (P : Fin n → BE) (p : Fin n → Bool)
    (hP : ∀ k, Witgen.BExpr.eval ctx (P k) = p k) (f : Fin n → ℕ) (hf : ∀ k, f k < 2 ^ 64)
    (d : ℕ) (hd : d < 2 ^ 64) :
    ∀ ks : List (Fin n),
      UIs ctx (ks.foldr (fun k acc => .ite (P k) (cst (f k)) acc) (cst d))
        ((ks.find? p).elim d f)
  | [] => UIs.cst hd
  | k :: ks => by
      have hrec := uis_foldr_pred P p hP f hf d hd ks
      simp only [List.foldr_cons, List.find?_cons]
      cases hk : p k with
      | true => exact UIs.ite_pos (by rw [hP k, hk]) (UIs.cst (hf k))
      | false => exact UIs.ite_neg (by rw [hP k, hk]) hrec

/-- The claim register's code selects exactly its claim. -/
theorem find?_finRange_claimCode (c : Option Model.Claim) :
    ((List.finRange nClaims).find? fun k => decide (claimCode c = k.val)) = c := by
  cases c with
  | none => rfl
  | some k => revert k; decide

theorem kindOfCode_str (c : Option Model.Claim) :
    decide (kindOfCode c = 0) = decide (Model.kindOf c = .str) := by
  cases c with
  | none => rfl
  | some k =>
      simp only [kindOfCode, kindCode, Model.kindOf, Option.elim]
      split_ifs <;> rfl

theorem kindOfCode_int (c : Option Model.Claim) :
    decide (kindOfCode c = 1) = decide (Model.kindOf c = .int) := by
  cases c with
  | none => rfl
  | some k =>
      simp only [kindOfCode, kindCode, Model.kindOf, Option.elim]
      split_ifs <;> rfl

theorem kindOfCode_bool (c : Option Model.Claim) :
    decide (kindOfCode c = 2) = decide (Model.kindOf c = .bool) := by
  cases c with
  | none => rfl
  | some k =>
      simp only [kindOfCode, kindCode, Model.kindOf, Option.elim]
      split_ifs <;> rfl

theorem kindOfCode_unk (c : Option Model.Claim) :
    decide (kindOfCode c = 3) = decide (Model.kindOf c = .unk) := by
  cases c with
  | none => rfl
  | some k =>
      simp only [kindOfCode, kindCode, Model.kindOf, Option.elim]
      split_ifs <;> rfl

theorem kindOfCode_lt (c : Option Model.Claim) : kindOfCode c < 2 ^ 64 := by
  cases c with
  | none => norm_num [kindOfCode]
  | some k => simp only [kindOfCode, kindCode, Option.elim]; split_ifs <;> norm_num

theorem subCode_lt (s : Option Model.Sub) : subCode s < 2 ^ 64 := by
  cases s with
  | none => norm_num [subCode, subNone, Model.nSub]
  | some k =>
      have := k.isLt; simp only [Model.nSub] at this
      simp only [subCode, Option.elim]; omega

theorem stCode_lt (s : Option Model.St) : stCode s < 2 ^ 64 := by
  cases s with
  | none => norm_num [stCode, stNone, Model.nSt]
  | some k => have := k.isLt; simp only [Model.nSt] at this; simp only [stCode, Option.elim]; omega

theorem claimCap_lt (k : Model.Claim) : Model.claimCap k < 2 ^ 64 := by
  have : Model.claimCap k ≤ 128 := by revert k; decide
  omega

/-! ### The fields of `sigOf`

`Model.signals` builds a literal structure, so each projection is definitionally the
expression the program mirrors. -/

section SigOf

variable (r : Model.Regs) (b : ℕ)

/-- The successor main state the program's `keyStart` sees. -/
def stNext (r : Model.Regs) (b : ℕ) : Model.St :=
  (Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Model.Sub.PLAIN)) r.st b).getD r.st

theorem sigOf_emit :
    (sigOf r b).emit =
      (((Model.inStr r.st && decide (r.sub = Model.Sub.PLAIN) && Model.isUnescaped b) ||
        (Model.inStr r.st && decide (r.sub = Model.Sub.ESC) && Model.isSimpleEsc b)) ||
       ((Model.inStr r.st && decide (r.sub = Model.Sub.H4) && Model.isHex b) ||
        (Model.inStr r.st && decide (r.sub = Model.Sub.C1) && Model.isCont b))) := by
  simp only [sigOf, Model.signals]
  cases Model.inStr r.st <;>
    simp only [Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false] <;>
    try rfl
  cases decide (r.sub = Model.Sub.PLAIN) <;> cases decide (r.sub = Model.Sub.ESC) <;>
    cases decide (r.sub = Model.Sub.H4) <;> cases decide (r.sub = Model.Sub.C1) <;>
    simp [Bool.or_assoc]

theorem sigOf_cp :
    (sigOf r b).cp =
      (if (Model.inStr r.st && decide (r.sub = Model.Sub.PLAIN) && Model.isUnescaped b) then b
       else if (Model.inStr r.st && decide (r.sub = Model.Sub.ESC) && Model.isSimpleEsc b) then
         Model.escVal b
       else if (Model.inStr r.st && decide (r.sub = Model.Sub.H4) && Model.isHex b) then
         16 * r.hexAcc + Model.hexVal b
       else if (Model.inStr r.st && decide (r.sub = Model.Sub.C1) && Model.isCont b) then
         Model.nonAsciiMarker
       else 0) := rfl

theorem sigOf_keyStart :
    (sigOf r b).keyStart = (decide (stNext r b = Model.St.KEY) && decide (r.st ≠ Model.St.KEY)) :=
  rfl

theorem sigOf_keyClose :
    (sigOf r b).keyClose =
      (decide (r.st = Model.St.KEY) && (b == Specs.JSON.quote) &&
        decide (r.sub = Model.Sub.PLAIN)) := rfl

theorem sigOf_match (k : Model.Claim) :
    (sigOf r b).match_[k] =
      ((sigOf r b).keyClose && r.m[k] && decide (r.kIdx = (Model.claimName k).length)) := by
  simp [sigOf, Model.signals]

theorem sigOf_digitEmit :
    (sigOf r b).digitEmit =
      (Model.isDigit b && (decide (r.st = Model.St.PVAL) || decide (r.st = Model.St.NSIGN) ||
        decide (r.st = Model.St.NINT))) := rfl

theorem sigOf_vEmit :
    (sigOf r b).vEmit =
      (((sigOf r b).emit && decide (r.st = Model.St.STR)) || (sigOf r b).digitEmit) := rfl

theorem sigOf_write :
    (sigOf r b).write =
      ((sigOf r b).vEmit &&
        (decide (Model.kindOf r.claim = .str) || decide (Model.kindOf r.claim = .int))) := rfl

theorem sigOf_valOut :
    (sigOf r b).valOut =
      (if ((sigOf r b).emit && decide (r.st = Model.St.STR)) then (sigOf r b).cp
       else if (sigOf r b).digitEmit then b - Specs.JSON.digit0 else 0) := rfl

theorem sigOf_minusFlag :
    (sigOf r b).minusFlag =
      (decide (r.st = Model.St.PVAL) && (b == Specs.JSON.minus)) := rfl

theorem sigOf_trueDone :
    (sigOf r b).trueDone = (decide (r.st = Model.St.T3) && (b == Specs.JSON.lowerE)) := rfl

theorem sigOf_hexVal : (sigOf r b).hexVal = Model.hexVal b := rfl

end SigOf

/-! ### Bounds and shape of the signals -/

private theorem beq_eq_decide (m n : ℕ) : (m == n) = decide (m = n) := by
  rw [Bool.eq_iff_iff]; simp

theorem escVal_lt (b : ℕ) : Model.escVal b < 256 := by
  simp only [Model.escVal, Specs.JSON.quote, Specs.JSON.backslash, Specs.JSON.slash,
    Specs.JSON.backspace, Specs.JSON.formfeed, Specs.JSON.lf, Specs.JSON.cr, Specs.JSON.tab]
  split_ifs <;> omega

theorem sigOf_cp_lt {r : Model.Regs} {b : ℕ} (hb : b < 256) (hh : r.hexAcc < 4096) :
    (sigOf r b).cp < 65536 := by
  rw [sigOf_cp]
  have h1 := hexVal_lt b
  have h2 := escVal_lt b
  split_ifs <;> [omega; omega; omega; (simp only [Model.nonAsciiMarker]; omega); omega]

theorem sigOf_valOut_lt {r : Model.Regs} {b : ℕ} (hb : b < 256) (hh : r.hexAcc < 4096) :
    (sigOf r b).valOut < 65536 := by
  rw [sigOf_valOut]
  have := sigOf_cp_lt hb hh
  split_ifs <;> omega

theorem digit0_le_of_digitEmit {r : Model.Regs} {b : ℕ} (h : (sigOf r b).digitEmit = true) :
    Specs.JSON.digit0 ≤ b := by
  rw [sigOf_digitEmit] at h
  simp only [Bool.and_eq_true, Model.isDigit, Specs.JSON.digit0, Specs.JSON.digit9,
    decide_eq_true_eq] at h
  simp only [Specs.JSON.digit0]
  omega

/-- The program's `keyStart` is the model's: on a rejected main transition both are off,
because the model's successor state is then the current one. -/
theorem eq_keyStart (r : Model.Regs) (b : ℕ) :
    (decide (stnOf r b = Model.St.KEY.val) && !decide (r.st = Model.St.KEY))
      = (sigOf r b).keyStart := by
  rw [sigOf_keyStart]
  cases h : Model.stepSt (Model.kindOf r.claim) (decide (r.sub = Model.Sub.PLAIN)) r.st b with
  | some s =>
      simp only [stnOf, stNext, h, stCode, Option.elim, Option.getD, ne_eq, decide_not,
        Fin.val_eq_val]
  | none =>
      simp only [stnOf, stNext, h, stCode, Option.elim, Option.getD, ne_eq, decide_not]
      by_cases hk : r.st = Model.St.KEY
      · simp [hk]
      · simp [hk, stNone, Model.nSt, Model.St.KEY]

theorem matchIdxOf_lt (r : Model.Regs) (b : ℕ) : matchIdxOf r b < 2 ^ 64 := by
  simp only [matchIdxOf]
  cases h : (List.finRange nClaims).find? fun k => (sigOf r b).match_[k] with
  | none => norm_num [claimCode, claimNone, Model.nClaims]
  | some k =>
      have := k.isLt; simp only [Model.nClaims] at this
      simp only [claimCode, Option.elim]; omega

/-! ### The constant name table -/

theorem evalList_map_const (ctx : Witgen.Ctx Fp) (l : List Fp) (n : ℕ) (hn : n < l.length) :
    Witgen.FExpr.evalList ctx n (l.map .const) = l[n] := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a l ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [List.map_cons, Witgen.FExpr.evalList, List.getElem_cons_succ]
          exact ih n (by simpa using hn)

theorem claimName_mem_le : ∀ (k : Model.Claim), ∀ x ∈ Model.claimName k, x ≤ 2 ^ 20 := by decide

theorem nameAt_le (k : Model.Claim) (t : ℕ) : Model.nameAt k t ≤ 2 ^ 20 := by
  simp only [Model.nameAt, List.getD]
  cases h : (Model.claimName k)[t]? with
  | none => simp only [h, Option.getD, Model.impossible]; omega
  | some x =>
      simp only [h, Option.getD]
      exact claimName_mem_le k x (List.mem_of_getElem? h)

/-- The claim-name table, read at the key index. -/
theorem uis_nameAtE {ctx : Witgen.Ctx Fp} {x : UE} {v : ℕ} (hx : UIs ctx x v)
    (hv : v < kIdxMax) (k : Model.Claim) : UIs ctx (nameAtE k x) (Model.nameAt k v) := by
  have hle := nameAt_le k v
  have hlt : Model.nameAt k v < circomPrime := by
    simp only [circomPrime] at *; omega
  refine ⟨by omega, ?_⟩
  have hidx : (Witgen.U64Expr.eval ctx x).toNat = v := by
    rw [hx.2, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hx.1]
  simp only [nameAtE, Witgen.U64Expr.eval, Witgen.FExpr.eval, hidx]
  rw [evalList_map_const ctx _ v (by
    simp only [List.length_map, Vector.length_toList]
    simpa [Model.kIdxMax] using hv)]
  have hget : (nameVec k).toList[v]'(by
      simp only [Vector.length_toList]; simpa [Model.kIdxMax] using hv)
      = ((Model.nameAt k v : ℕ) : Fp) := by
    simp only [nameVec, Vector.getElem_toList, Vector.getElem_ofFn]
  rw [hget]
  simp only [ff_val, ZMod.val_natCast_of_lt hlt]

/-! ### The register update of a step -/

theorem anyEq_st_inVal (s : Model.St) :
    ([Model.St.PRE.val, Model.St.OBJ.val, Model.St.KEY.val, Model.St.AKEY.val, Model.St.PVAL.val,
      Model.St.AVAL.val, Model.St.SEP.val, Model.St.END.val].any fun n => decide (s.val = n))
      = !(decide (s ≠ Model.St.PRE) && decide (s ≠ Model.St.OBJ) && decide (s ≠ Model.St.KEY) &&
          decide (s ≠ Model.St.AKEY) && decide (s ≠ Model.St.PVAL) &&
          decide (s ≠ Model.St.AVAL) && decide (s ≠ Model.St.SEP) &&
          decide (s ≠ Model.St.END)) := by
  revert s; decide

theorem nextRegs_of_not_adv {r : Model.Regs} {b : ℕ} {active : Bool}
    (h : (active && (Model.step r b).isSome) = false) : nextRegs r b active = r := by
  cases active <;> cases hs : Model.step r b <;> simp_all [nextRegs]

theorem nextRegs_of_adv {r r' : Model.Regs} {b : ℕ} {active : Bool}
    (hact : active = true) (hs : Model.step r b = some r') : nextRegs r b active = r' := by
  simp [nextRegs, hact, hs]

/-- Every field of the model's step, read off in the program's vocabulary. -/
theorem step_some_fields {r r' : Model.Regs} {b : ℕ} (h : Model.step r b = some r') :
    r'.st.val = stnOf r b ∧ r'.sub.val = subnOf r b ∧
    r'.hexAcc = (if (decide (r.sub = Model.Sub.H1) ||
        (decide (r.sub = Model.Sub.H2) || decide (r.sub = Model.Sub.H3)))
      then 16 * r.hexAcc + Model.hexVal b else 0) ∧
    r'.kIdx = (if r.st = Model.St.KEY then
        min (r.kIdx + ub (sigOf r b).emit) (kIdxMax - 1) else 0) ∧
    claimCode r'.claim = (if (sigOf r b).keyClose then matchIdxOf r b
      else if (sigOf r b).keyStart then claimNone else claimCode r.claim) ∧
    r'.ofs = min ((if (decide (r.st ≠ Model.St.PRE) && decide (r.st ≠ Model.St.OBJ) &&
        decide (r.st ≠ Model.St.KEY) && decide (r.st ≠ Model.St.AKEY) &&
        decide (r.st ≠ Model.St.PVAL) && decide (r.st ≠ Model.St.AVAL) &&
        decide (r.st ≠ Model.St.SEP) && decide (r.st ≠ Model.St.END)) then r.ofs else 0)
      + ub (sigOf r b).vEmit) (ofsMax - 1) ∧
    r'.nMem = r.nMem + ub (sigOf r b).keyStart ∧
    ∀ k : Model.Claim, r'.m[k] = (if (sigOf r b).keyStart then true
      else if r.st = Model.St.KEY then
        (r.m[k] && (!(sigOf r b).emit ||
          decide ((sigOf r b).cp = Model.nameAt k r.kIdx))) else false) := by
  simp only [Model.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨sub', hsub, st', hst, h⟩ := h
  have hr' := ite_none_some _ _ _ h
  have hsig : sigOf r b = Model.signals r b st' := by simp only [sigOf, hst, Option.getD]
  have hsn : stnOf r b = st'.val := by simp only [stnOf, hst, stCode, Option.elim]
  have hsb : subnOf r b = sub'.val := by simp only [subnOf, hsub, subCode, Option.elim]
  subst hr'
  refine ⟨hsn.symm, hsb.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsig, signals_hexVal, Bool.or_assoc]
  · simp only [hsig, ub]
  · simp only [matchIdxOf, hsig]
    split_ifs <;> simp [claimCode]
  · simp only [hsig, ub]
  · simp only [hsig, ub]
  · intro k
    simp only [hsig]
    simp

/-! ### The byte classes

Each class condition of the program decides its `Model.lean` counterpart. -/

section Classes

variable {ctx : Witgen.Ctx Fp} {x : UE} {v : ℕ}

theorem eval_cWs (hx : UIs ctx x v) : Witgen.BExpr.eval ctx (cWs x) = Model.isWs v := by
  rw [cWs, eval_anyEq hx _ (by decide), Bool.eq_iff_iff]
  simp only [Model.isWs, Specs.JSON.space, Specs.JSON.tab, Specs.JSON.lf, Specs.JSON.cr,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_cons, List.any_nil]
  tauto

theorem eval_cDigit (hx : UIs ctx x v) : Witgen.BExpr.eval ctx (cDigit x) = Model.isDigit v := by
  rw [cDigit, eval_rngN hx (by norm_num [Specs.JSON.digit0]) (by norm_num [Specs.JSON.digit9])]
  simp [Model.isDigit]

theorem eval_cDigitNz (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (cDigitNz x) = Model.isDigitNz v := by
  rw [cDigitNz, eval_rngN hx (by norm_num [Specs.JSON.digit0]) (by norm_num [Specs.JSON.digit9]),
    Bool.eq_iff_iff]
  simp only [Model.isDigitNz, Specs.JSON.digit0, Specs.JSON.digit9, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

theorem eval_cUpperHex (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (cUpperHex x) = Model.isUpperHex v := by
  rw [cUpperHex, eval_rngN hx (by norm_num [Specs.JSON.upperA]) (by norm_num [Specs.JSON.upperF])]
  simp [Model.isUpperHex]

theorem eval_cLowerHex (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (cLowerHex x) = Model.isLowerHex v := by
  rw [cLowerHex, eval_rngN hx (by norm_num [Specs.JSON.lowerA]) (by norm_num [Specs.JSON.lowerF])]
  simp [Model.isLowerHex]

theorem eval_cHex (hx : UIs ctx x v) : Witgen.BExpr.eval ctx (cHex x) = Model.isHex v := by
  rw [cHex, eval_bor, eval_bor, eval_cDigit hx, eval_cUpperHex hx, eval_cLowerHex hx,
    Bool.eq_iff_iff]
  simp only [Model.isHex, Bool.or_eq_true]
  tauto

theorem eval_cUnesc (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (cUnesc x) = Model.isUnescaped v := by
  rw [cUnesc, show Witgen.BExpr.eval ctx (.and (rngN x Specs.JSON.space 0x7F)
        (.and (.not (eqn x Specs.JSON.quote)) (.not (eqn x Specs.JSON.backslash))))
      = (Witgen.BExpr.eval ctx (rngN x Specs.JSON.space 0x7F)
        && (!Witgen.BExpr.eval ctx (eqn x Specs.JSON.quote)
          && !Witgen.BExpr.eval ctx (eqn x Specs.JSON.backslash))) from rfl,
    eval_rngN hx (by norm_num [Specs.JSON.space]) (by norm_num),
    eval_eqn hx (by norm_num [Specs.JSON.quote]),
    eval_eqn hx (by norm_num [Specs.JSON.backslash]), Bool.eq_iff_iff]
  simp only [Model.isUnescaped, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not]
  tauto

theorem eval_cExpL (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (cExpL x) = Model.isExpLetter v := by
  rw [cExpL, eval_bor, eval_eqn hx (by norm_num [Specs.JSON.lowerE]),
    eval_eqn hx (by norm_num [Specs.JSON.upperE]), Bool.eq_iff_iff]
  simp [Model.isExpLetter]

theorem eval_cSign (hx : UIs ctx x v) : Witgen.BExpr.eval ctx (cSign x) = Model.isSign v := by
  rw [cSign, eval_bor, eval_eqn hx (by norm_num [Specs.JSON.plus]),
    eval_eqn hx (by norm_num [Specs.JSON.minus]), Bool.eq_iff_iff]
  simp [Model.isSign]

theorem eval_cSimpleEsc (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (cSimpleEsc x) = Model.isSimpleEsc v := by
  rw [cSimpleEsc, eval_anyEq hx _ (by decide), Bool.eq_iff_iff]
  simp only [Model.isSimpleEsc, Specs.JSON.quote, Specs.JSON.backslash, Specs.JSON.slash,
    Specs.JSON.lowerB, Specs.JSON.lowerF, Specs.JSON.lowerN, Specs.JSON.lowerR,
    Specs.JSON.lowerT, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_cons,
    List.any_nil]
  tauto

theorem eval_cCont (hx : UIs ctx x v) : Witgen.BExpr.eval ctx (cCont x) = Model.isCont v := by
  rw [cCont, eval_rngN hx (by norm_num) (by norm_num)]
  simp [Model.isCont]

theorem eval_cLead2 (hx : UIs ctx x v) : Witgen.BExpr.eval ctx (cLead2 x) = Model.isLead2 v := by
  rw [cLead2, eval_rngN hx (by norm_num) (by norm_num)]
  simp [Model.isLead2]

theorem eval_cLead3 (hx : UIs ctx x v) : Witgen.BExpr.eval ctx (cLead3 x) = Model.isLead3 v := by
  rw [cLead3, eval_bor, eval_rngN hx (by norm_num) (by norm_num),
    eval_rngN hx (by norm_num) (by norm_num)]
  simp [Model.isLead3]

theorem eval_cLead4 (hx : UIs ctx x v) : Witgen.BExpr.eval ctx (cLead4 x) = Model.isLead4 v := by
  rw [cLead4, eval_rngN hx (by norm_num) (by norm_num)]
  simp [Model.isLead4]

theorem eval_cA0BF (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (cA0BF x) = Model.isContA0BF v := by
  rw [cA0BF, eval_rngN hx (by norm_num) (by norm_num)]
  simp [Model.isContA0BF]

theorem eval_c809F (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (c809F x) = Model.isCont809F v := by
  rw [c809F, eval_rngN hx (by norm_num) (by norm_num)]
  simp [Model.isCont809F]

theorem eval_c90BF (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (c90BF x) = Model.isCont90BF v := by
  rw [c90BF, eval_rngN hx (by norm_num) (by norm_num)]
  simp [Model.isCont90BF]

theorem eval_c808F (hx : UIs ctx x v) :
    Witgen.BExpr.eval ctx (c808F x) = Model.isCont808F v := by
  rw [c808F, eval_rngN hx (by norm_num) (by norm_num)]
  simp [Model.isCont808F]

/-- The simple-escape table. -/
theorem uis_escValE (hx : UIs ctx x v) : UIs ctx (escValE x) (Model.escVal v) := by
  have he : ∀ n : ℕ, n < 2 ^ 64 → Witgen.BExpr.eval ctx (eqn x n) = decide (v = n) :=
    fun n hn => eval_eqn hx hn
  simp only [escValE, chain, List.foldr_cons, List.foldr_nil, Model.escVal]
  refine UIs.ite' (he _ (by norm_num [Specs.JSON.quote])) (UIs.cst (by norm_num [Specs.JSON.quote]))
    (UIs.ite' (he _ (by norm_num [Specs.JSON.backslash]))
      (UIs.cst (by norm_num [Specs.JSON.backslash]))
      (UIs.ite' (he _ (by norm_num [Specs.JSON.slash])) (UIs.cst (by norm_num [Specs.JSON.slash]))
        (UIs.ite' (he _ (by norm_num [Specs.JSON.lowerB]))
          (UIs.cst (by norm_num [Specs.JSON.backspace]))
          (UIs.ite' (he _ (by norm_num [Specs.JSON.lowerF]))
            (UIs.cst (by norm_num [Specs.JSON.formfeed]))
            (UIs.ite' (he _ (by norm_num [Specs.JSON.lowerN])) (UIs.cst (by norm_num [Specs.JSON.lf]))
              (UIs.ite' (he _ (by norm_num [Specs.JSON.lowerR]))
                (UIs.cst (by norm_num [Specs.JSON.cr]))
                (UIs.ite' (he _ (by norm_num [Specs.JSON.lowerT]))
                  (UIs.cst (by norm_num [Specs.JSON.tab])) (UIs.cst (by norm_num)))))))))
    |>.congr ?_
  simp only [decide_eq_true_eq, beq_iff_eq]

/-- The hex-digit table. -/
theorem uis_hexValE (hx : UIs ctx x v) : UIs ctx (hexValE x) (Model.hexVal v) := by
  simp only [hexValE, chain, List.foldr_cons, List.foldr_nil, Model.hexVal]
  by_cases h1 : Model.isDigit v
  · have hle : Specs.JSON.digit0 ≤ v := by
      simp only [Model.isDigit, Specs.JSON.digit0, Specs.JSON.digit9, Bool.and_eq_true,
        decide_eq_true_eq] at h1 ⊢
      omega
    rw [if_pos h1]
    exact UIs.ite_pos (by rw [eval_cDigit hx, h1]) (UIs.subN hx hle)
  · rw [if_neg h1]
    refine UIs.ite_neg (by rw [eval_cDigit hx]; simpa using h1) ?_
    by_cases h2 : Model.isUpperHex v
    · have hle : Specs.JSON.upperA - 10 ≤ v := by
        simp only [Model.isUpperHex, Specs.JSON.upperA, Specs.JSON.upperF, Bool.and_eq_true,
          decide_eq_true_eq] at h2 ⊢
        omega
      rw [if_pos h2]
      refine (UIs.ite_pos (by rw [eval_cUpperHex hx, h2]) (UIs.subN hx hle)).congr ?_
      simp only [Specs.JSON.upperA]
      simp only [Model.isUpperHex, Specs.JSON.upperA, Specs.JSON.upperF, Bool.and_eq_true,
        decide_eq_true_eq] at h2
      omega
    · rw [if_neg h2]
      refine UIs.ite_neg (by rw [eval_cUpperHex hx]; simpa using h2) ?_
      by_cases h3 : Model.isLowerHex v
      · have hle : Specs.JSON.lowerA - 10 ≤ v := by
          simp only [Model.isLowerHex, Specs.JSON.lowerA, Specs.JSON.lowerF, Bool.and_eq_true,
            decide_eq_true_eq] at h3 ⊢
          omega
        rw [if_pos h3]
        refine (UIs.ite_pos (by rw [eval_cLowerHex hx, h3]) (UIs.subN hx hle)).congr ?_
        simp only [Specs.JSON.lowerA]
        simp only [Model.isLowerHex, Specs.JSON.lowerA, Specs.JSON.lowerF, Bool.and_eq_true,
          decide_eq_true_eq] at h3
        omega
      · rw [if_neg h3]
        exact UIs.ite_neg (by rw [eval_cLowerHex hx]; simpa using h3) (UIs.cst (by norm_num))

end Classes

set_option maxHeartbeats 1000000 in
/-- Evaluating one position's block: the `blockSize` locals it binds are exactly
`blockVal` of the registers before the position, the byte, and the activity flag. -/
theorem evalSteps_stepBlock (input : Var Input Fp) (env : ProverEnvironment Fp)
    {i : ℕ} (hi : i < bufferLen) {b : ℕ} (hb : b < 256)
    (hbeq : Witness.bytesOf input env i = b)
    {active : Bool} (hact : decide (i < Witness.lenOf input env) = active)
    (hlen : Witness.lenOf input env ≤ bufferLen)
    {L : Array (Fp ⊕ UInt64)} (hL : L.size = nRegs + blockSize * i)
    {r : Model.Regs} (hregs : HoldsRegs L i r)
    (hhex : r.hexAcc < 4096) (hkidx : r.kIdx ≤ kIdxMax - 1) (hofs : r.ofs ≤ ofsMax - 1)
    (hnmem : r.nMem ≤ bufferLen) :
    evalSteps env (stepBlock input i) L
      = L ++ accOf (blockVal r b active) blockSize := by
  have hclaim64 : claimCode r.claim < 2 ^ 64 := by
    cases hc : r.claim with
    | none => simp only [claimCode, hc, Option.elim, claimNone, Model.nClaims]; norm_num
    | some k =>
        have := k.isLt
        simp only [Model.nClaims] at this
        simp only [claimCode, hc, Option.elim]; omega
  -- the registers of block `i`, read back in any context inside the block
  have gST : ∀ k, UIs (blockCtx env L (blockVal r b active) k) (reg i rST) r.st.val :=
    fun k => uis_reg hL _ k (by decide) (lt_trans r.st.isLt nSt_lt64) hregs.1
  have gSUB : ∀ k, UIs (blockCtx env L (blockVal r b active) k) (reg i rSUB) r.sub.val :=
    fun k => uis_reg hL _ k (by decide) (lt_trans r.sub.isLt nSub_lt64) hregs.2.1
  have gHEX : ∀ k, UIs (blockCtx env L (blockVal r b active) k) (reg i rHEXACC) r.hexAcc :=
    fun k => uis_reg hL _ k (by decide) (by omega) hregs.2.2.1
  have gKIDX : ∀ k, UIs (blockCtx env L (blockVal r b active) k) (reg i rKIDX) r.kIdx :=
    fun k => uis_reg hL _ k (by decide)
      (by simp only [Model.kIdxMax] at hkidx; omega) hregs.2.2.2.1
  have gCLAIM : ∀ k, UIs (blockCtx env L (blockVal r b active) k) (reg i rCLAIM)
      (claimCode r.claim) :=
    fun k => uis_reg hL _ k (by decide) hclaim64 hregs.2.2.2.2.1
  have gOFS : ∀ k, UIs (blockCtx env L (blockVal r b active) k) (reg i rOFS) r.ofs :=
    fun k => uis_reg hL _ k (by decide)
      (by simp only [Model.ofsMax] at hofs; omega) hregs.2.2.2.2.2.1
  have gNMEM : ∀ k, UIs (blockCtx env L (blockVal r b active) k) (reg i rNMEM) r.nMem :=
    fun k => uis_reg hL _ k (by decide)
      (by simp only [bufferLen] at hnmem; omega) hregs.2.2.2.2.2.2.1
  have gM : ∀ (j : ℕ) (k : ℕ) (hk : k < nClaims),
      UIs (blockCtx env L (blockVal r b active) j) (reg i (rM + k)) (ub (r.m[k]'hk)) := by
    intro j k hk
    refine uis_reg hL _ j (by simp only [nRegs, rM, Model.nClaims] at hk ⊢; omega) (ub_lt _) ?_
    have h := hregs.2.2.2.2.2.2.2 ⟨k, hk⟩
    simp only [Fin.val_mk] at h
    rw [h]
    cases hm : r.m[k]'hk <;> simp [ub, hm]
  -- the input reads
  have gLEN : ∀ k, UIs (blockCtx env L (blockVal r b active) k) (lenE input)
      (Witness.lenOf input env) := by
    intro k
    exact UIs.valExpr (by simp only [bufferLen] at hlen; omega) rfl
  have gB : ∀ k, UIs (blockCtx env L (blockVal r b active) k) (.val (byteAt input i)) b := by
    intro k
    refine UIs.valExpr (by omega) ?_
    rw [← hbeq]
    simp only [byteAt, Witness.bytesOf, dif_pos hi]
    rfl
  -- the signals, read back in any later context of the block
  have gS : ∀ (k m : ℕ), m < k → blockVal r b active m < 2 ^ 64 →
      UIs (blockCtx env L (blockVal r b active) k) (sigl i m) (blockVal r b active m) :=
    fun k m hm hlt => uis_sigl hL _ hm hlt
  have hStLt : ∀ s : Model.St, (s.val : ℕ) < 2 ^ 64 := fun s => lt_trans s.isLt nSt_lt64
  have hSubLt : ∀ s : Model.Sub, (s.val : ℕ) < 2 ^ 64 := fun s => lt_trans s.isLt nSub_lt64
  have gBS : ∀ k, 1 < k → UIs (blockCtx env L (blockVal r b active) k) (sigl i sB) b :=
    fun k hk => gS k 1 hk (by simp only [blockVal]; omega)
  have fS : ∀ (k m : ℕ) (c : Bool), m < k → blockVal r b active m = ub c →
      Witgen.BExpr.eval (blockCtx env L (blockVal r b active) k) (eqn (sigl i m) 1) = c := by
    intro k m c hm hv
    exact eval_flagN (hv ▸ gS k m hm (by rw [hv]; exact ub_lt c))
  have eST : ∀ (k : ℕ) (s : Model.St),
      Witgen.BExpr.eval (blockCtx env L (blockVal r b active) k) (eqn (reg i rST) s.val)
        = decide (r.st = s) := by
    intro k s
    rw [eval_eqn (gST k) (hStLt s)]
    simp [Fin.ext_iff]
  have eSUB : ∀ (k : ℕ) (s : Model.Sub),
      Witgen.BExpr.eval (blockCtx env L (blockVal r b active) k) (eqn (reg i rSUB) s.val)
        = decide (r.sub = s) := by
    intro k s
    rw [eval_eqn (gSUB k) (hSubLt s)]
    simp [Fin.ext_iff]
  have eB : ∀ (k n : ℕ), 1 < k → n < 2 ^ 64 →
      Witgen.BExpr.eval (blockCtx env L (blockVal r b active) k) (eqn (sigl i sB) n)
        = decide (b = n) := fun k n hk hn => eval_eqn (gBS k hk) hn
  -- the values, step by step
  have v0 : UIs (blockCtx env L (blockVal r b active) 0)
      (toU (.lt (cst i) (lenE input))) (ub active) :=
    UIs.toU' (by
      rw [eval_ltU (UIs.cst (show i < 2 ^ 64 by simp only [bufferLen] at hi; omega)) (gLEN 0)]
      exact hact)
  have v1 : UIs (blockCtx env L (blockVal r b active) 1) (.val (byteAt input i)) b := gB 1
  have v2 : UIs (blockCtx env L (blockVal r b active) 2)
      (toU (cWs (sigl i sB))) (ub (Model.isWs b)) :=
    UIs.toU' (eval_cWs (gBS 2 (by norm_num)))
  have v3 : UIs (blockCtx env L (blockVal r b active) 3)
      (toU (cDigit (sigl i sB))) (ub (Model.isDigit b)) :=
    UIs.toU' (eval_cDigit (gBS 3 (by norm_num)))
  have v4 : UIs (blockCtx env L (blockVal r b active) 4)
      (toU (cDigitNz (sigl i sB))) (ub (Model.isDigitNz b)) :=
    UIs.toU' (eval_cDigitNz (gBS 4 (by norm_num)))
  have v5 : UIs (blockCtx env L (blockVal r b active) 5)
      (toU (cHex (sigl i sB))) (ub (Model.isHex b)) :=
    UIs.toU' (eval_cHex (gBS 5 (by norm_num)))
  have v6 : UIs (blockCtx env L (blockVal r b active) 6)
      (toU (cUnesc (sigl i sB))) (ub (Model.isUnescaped b)) :=
    UIs.toU' (eval_cUnesc (gBS 6 (by norm_num)))
  have v7 : UIs (blockCtx env L (blockVal r b active) 7)
      (toU (cExpL (sigl i sB))) (ub (Model.isExpLetter b)) :=
    UIs.toU' (eval_cExpL (gBS 7 (by norm_num)))
  have v8 : UIs (blockCtx env L (blockVal r b active) 8)
      (toU (cSign (sigl i sB))) (ub (Model.isSign b)) :=
    UIs.toU' (eval_cSign (gBS 8 (by norm_num)))
  have v9 : UIs (blockCtx env L (blockVal r b active) 9)
      (toU (cSimpleEsc (sigl i sB))) (ub (Model.isSimpleEsc b)) :=
    UIs.toU' (eval_cSimpleEsc (gBS 9 (by norm_num)))
  have v10 : UIs (blockCtx env L (blockVal r b active) 10)
      (toU (cCont (sigl i sB))) (ub (Model.isCont b)) :=
    UIs.toU' (eval_cCont (gBS 10 (by norm_num)))
  have v11 : UIs (blockCtx env L (blockVal r b active) 11)
      (toU (cLead2 (sigl i sB))) (ub (Model.isLead2 b)) :=
    UIs.toU' (eval_cLead2 (gBS 11 (by norm_num)))
  have v12 : UIs (blockCtx env L (blockVal r b active) 12)
      (toU (cLead3 (sigl i sB))) (ub (Model.isLead3 b)) :=
    UIs.toU' (eval_cLead3 (gBS 12 (by norm_num)))
  have v13 : UIs (blockCtx env L (blockVal r b active) 13)
      (toU (cLead4 (sigl i sB))) (ub (Model.isLead4 b)) :=
    UIs.toU' (eval_cLead4 (gBS 13 (by norm_num)))
  have v14 : UIs (blockCtx env L (blockVal r b active) 14)
      (toU (cA0BF (sigl i sB))) (ub (Model.isContA0BF b)) :=
    UIs.toU' (eval_cA0BF (gBS 14 (by norm_num)))
  have v15 : UIs (blockCtx env L (blockVal r b active) 15)
      (toU (c809F (sigl i sB))) (ub (Model.isCont809F b)) :=
    UIs.toU' (eval_c809F (gBS 15 (by norm_num)))
  have v16 : UIs (blockCtx env L (blockVal r b active) 16)
      (toU (c90BF (sigl i sB))) (ub (Model.isCont90BF b)) :=
    UIs.toU' (eval_c90BF (gBS 16 (by norm_num)))
  have v17 : UIs (blockCtx env L (blockVal r b active) 17)
      (toU (c808F (sigl i sB))) (ub (Model.isCont808F b)) :=
    UIs.toU' (eval_c808F (gBS 17 (by norm_num)))
  have v18 : UIs (blockCtx env L (blockVal r b active) 18)
      (toU (bor (eqn (reg i rST) Model.St.KEY.val) (eqn (reg i rST) Model.St.STR.val)))
      (ub (Model.inStr r.st)) :=
    UIs.toU' (by rw [eval_bor, eST 18 Model.St.KEY, eST 18 Model.St.STR]; rfl)
  have v19 : UIs (blockCtx env L (blockVal r b active) 19)
      (toU (.and (eqn (sigl i sSTRNOW) 1)
        (.and (eqn (reg i rSUB) Model.Sub.PLAIN.val) (eqn (sigl i sUNESC) 1))))
      (ub (Model.inStr r.st && decide (r.sub = Model.Sub.PLAIN) && Model.isUnescaped b)) :=
    UIs.toU' (by
      rw [eval_and, eval_and, fS 19 sSTRNOW _ (by decide) rfl, eSUB 19 Model.Sub.PLAIN,
        fS 19 sUNESC _ (by decide) rfl, Bool.and_assoc])
  have v20 : UIs (blockCtx env L (blockVal r b active) 20)
      (toU (.and (eqn (sigl i sSTRNOW) 1)
        (.and (eqn (reg i rSUB) Model.Sub.ESC.val) (eqn (sigl i sSIMPLEESC) 1))))
      (ub (Model.inStr r.st && decide (r.sub = Model.Sub.ESC) && Model.isSimpleEsc b)) :=
    UIs.toU' (by
      rw [eval_and, eval_and, fS 20 sSTRNOW _ (by decide) rfl, eSUB 20 Model.Sub.ESC,
        fS 20 sSIMPLEESC _ (by decide) rfl, Bool.and_assoc])
  have v21 : UIs (blockCtx env L (blockVal r b active) 21)
      (toU (.and (eqn (sigl i sSTRNOW) 1)
        (.and (eqn (reg i rSUB) Model.Sub.H4.val) (eqn (sigl i sHEX) 1))))
      (ub (Model.inStr r.st && decide (r.sub = Model.Sub.H4) && Model.isHex b)) :=
    UIs.toU' (by
      rw [eval_and, eval_and, fS 21 sSTRNOW _ (by decide) rfl, eSUB 21 Model.Sub.H4,
        fS 21 sHEX _ (by decide) rfl, Bool.and_assoc])
  have v22 : UIs (blockCtx env L (blockVal r b active) 22)
      (toU (.and (eqn (sigl i sSTRNOW) 1)
        (.and (eqn (reg i rSUB) Model.Sub.C1.val) (eqn (sigl i sCONT) 1))))
      (ub (Model.inStr r.st && decide (r.sub = Model.Sub.C1) && Model.isCont b)) :=
    UIs.toU' (by
      rw [eval_and, eval_and, fS 22 sSTRNOW _ (by decide) rfl, eSUB 22 Model.Sub.C1,
        fS 22 sCONT _ (by decide) rfl, Bool.and_assoc])
  have v23 : UIs (blockCtx env L (blockVal r b active) 23)
      (toU (bor (bor (eqn (sigl i sEMITPLAIN) 1) (eqn (sigl i sEMITESC) 1))
        (bor (eqn (sigl i sEMITU) 1) (eqn (sigl i sEMITUTF8) 1))))
      (ub (sigOf r b).emit) :=
    UIs.toU' (by
      rw [eval_bor, eval_bor, eval_bor, fS 23 sEMITPLAIN _ (by decide) rfl,
        fS 23 sEMITESC _ (by decide) rfl, fS 23 sEMITU _ (by decide) rfl,
        fS 23 sEMITUTF8 _ (by decide) rfl, sigOf_emit])
  have v24 : UIs (blockCtx env L (blockVal r b active) 24)
      (hexValE (sigl i sB)) (Model.hexVal b) := uis_hexValE (gBS 24 (by norm_num))
  have hHV : UIs (blockCtx env L (blockVal r b active) 25) (sigl i sHV) (Model.hexVal b) :=
    gS 25 24 (by norm_num) (by simp only [blockVal]; have := hexVal_lt b; omega)
  have v25 : UIs (blockCtx env L (blockVal r b active) 25)
      (.ite (eqn (sigl i sEMITPLAIN) 1) (sigl i sB)
        (.ite (eqn (sigl i sEMITESC) 1) (escValE (sigl i sB))
          (.ite (eqn (sigl i sEMITU) 1) (.add (.mul (cst 16) (reg i rHEXACC)) (sigl i sHV))
            (.ite (eqn (sigl i sEMITUTF8) 1) (cst Model.nonAsciiMarker) (cst 0)))))
      ((sigOf r b).cp) := by
    have hhv := hexVal_lt b
    rw [sigOf_cp]
    exact UIs.ite' (fS 25 sEMITPLAIN _ (by decide) rfl) (gBS 25 (by norm_num))
      (UIs.ite' (fS 25 sEMITESC _ (by decide) rfl) (uis_escValE (gBS 25 (by norm_num)))
        (UIs.ite' (fS 25 sEMITU _ (by decide) rfl)
          (UIs.add (UIs.mul (UIs.cst (by norm_num)) (gHEX 25) (by omega)) hHV (by omega))
          (UIs.ite' (fS 25 sEMITUTF8 _ (by decide) rfl)
            (UIs.cst (by norm_num [Model.nonAsciiMarker])) (UIs.cst (by norm_num)))))
  have cSub : ∀ s : Model.Sub, Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 26)
      (eqn (reg i rSUB) s.val) = decide (r.sub = s) := eSUB 26
  have cByte : ∀ n : ℕ, n < 2 ^ 64 →
      Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 26) (eqn (sigl i sB) n)
        = decide (b = n) := fun n hn => eB 26 n (by norm_num) hn
  have cF : ∀ (m : ℕ) (c : Bool), m < 26 → blockVal r b active m = ub c →
      Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 26) (eqn (sigl i m) 1) = c :=
    fun m c hm hv => fS 26 m c hm hv
  have kSub : ∀ s : Model.Sub, UIs (blockCtx env L (blockVal r b active) 26) (cst s.val) s.val :=
    fun s => UIs.cst (hSubLt s)
  have kNone : UIs (blockCtx env L (blockVal r b active) 26) (cst subNone) subNone :=
    UIs.cst (by norm_num [subNone, Model.nSub])
  have v26 : UIs (blockCtx env L (blockVal r b active) 26)
      (chain [(BExpr.not (eqn (sigl i sSTRNOW) 1), cst Model.Sub.PLAIN.val),
          (eqn (reg i rSUB) Model.Sub.PLAIN.val, chain [(eqn (sigl i sB) quote, cst Model.Sub.PLAIN.val), (eqn (sigl i sUNESC) 1, cst Model.Sub.PLAIN.val), (eqn (sigl i sB) backslash, cst Model.Sub.ESC.val), (eqn (sigl i sLEAD2) 1, cst Model.Sub.C1.val), (eqn (sigl i sB) 0xE0, cst Model.Sub.E0s.val), (eqn (sigl i sLEAD3) 1, cst Model.Sub.C2.val), (eqn (sigl i sB) 0xED, cst Model.Sub.EDs.val), (eqn (sigl i sB) 0xF0, cst Model.Sub.F0s.val), (eqn (sigl i sLEAD4) 1, cst Model.Sub.C3.val), (eqn (sigl i sB) 0xF4, cst Model.Sub.F4s.val)] (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.ESC.val, chain [(eqn (sigl i sSIMPLEESC) 1, cst Model.Sub.PLAIN.val), (eqn (sigl i sB) lowerU, cst Model.Sub.H1.val)] (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.H1.val, U64Expr.ite (eqn (sigl i sHEX) 1) (cst Model.Sub.H2.val) (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.H2.val, U64Expr.ite (eqn (sigl i sHEX) 1) (cst Model.Sub.H3.val) (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.H3.val, U64Expr.ite (eqn (sigl i sHEX) 1) (cst Model.Sub.H4.val) (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.H4.val, U64Expr.ite (eqn (sigl i sHEX) 1) (cst Model.Sub.PLAIN.val) (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.C1.val, U64Expr.ite (eqn (sigl i sCONT) 1) (cst Model.Sub.PLAIN.val) (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.C2.val, U64Expr.ite (eqn (sigl i sCONT) 1) (cst Model.Sub.C1.val) (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.C3.val, U64Expr.ite (eqn (sigl i sCONT) 1) (cst Model.Sub.C2.val) (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.E0s.val, U64Expr.ite (eqn (sigl i sA0BF) 1) (cst Model.Sub.C1.val) (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.EDs.val, U64Expr.ite (eqn (sigl i s809F) 1) (cst Model.Sub.C1.val) (cst subNone)),
          (eqn (reg i rSUB) Model.Sub.F0s.val, U64Expr.ite (eqn (sigl i s90BF) 1) (cst Model.Sub.C2.val) (cst subNone))]
        (U64Expr.ite (eqn (sigl i s808F) 1) (cst Model.Sub.C2.val) (cst subNone)))
      (subnOf r b) := by
    refine (UIs.chain_cons (by rw [eval_not, cF sSTRNOW _ (by decide) rfl]) (kSub Model.Sub.PLAIN)
        (UIs.chain_cons (cSub Model.Sub.PLAIN) (UIs.chain_cons (cByte _ (by norm_num [Specs.JSON.quote])) (kSub Model.Sub.PLAIN) (UIs.chain_cons (cF sUNESC _ (by decide) rfl) (kSub Model.Sub.PLAIN) (UIs.chain_cons (cByte _ (by norm_num [Specs.JSON.backslash])) (kSub Model.Sub.ESC) (UIs.chain_cons (cF sLEAD2 _ (by decide) rfl) (kSub Model.Sub.C1) (UIs.chain_cons (cByte _ (by norm_num)) (kSub Model.Sub.E0s) (UIs.chain_cons (cF sLEAD3 _ (by decide) rfl) (kSub Model.Sub.C2) (UIs.chain_cons (cByte _ (by norm_num)) (kSub Model.Sub.EDs) (UIs.chain_cons (cByte _ (by norm_num)) (kSub Model.Sub.F0s) (UIs.chain_cons (cF sLEAD4 _ (by decide) rfl) (kSub Model.Sub.C3) (UIs.chain_cons (cByte _ (by norm_num)) (kSub Model.Sub.F4s) (UIs.chain_nil kNone)))))))))))
        (UIs.chain_cons (cSub Model.Sub.ESC) (UIs.chain_cons (cF sSIMPLEESC _ (by decide) rfl) (kSub Model.Sub.PLAIN) (UIs.chain_cons (cByte _ (by norm_num [Specs.JSON.lowerU])) (kSub Model.Sub.H1) (UIs.chain_nil kNone)))
        (UIs.chain_cons (cSub Model.Sub.H1) (UIs.ite' (cF sHEX _ (by decide) rfl) (kSub Model.Sub.H2) kNone)
        (UIs.chain_cons (cSub Model.Sub.H2) (UIs.ite' (cF sHEX _ (by decide) rfl) (kSub Model.Sub.H3) kNone)
        (UIs.chain_cons (cSub Model.Sub.H3) (UIs.ite' (cF sHEX _ (by decide) rfl) (kSub Model.Sub.H4) kNone)
        (UIs.chain_cons (cSub Model.Sub.H4) (UIs.ite' (cF sHEX _ (by decide) rfl) (kSub Model.Sub.PLAIN) kNone)
        (UIs.chain_cons (cSub Model.Sub.C1) (UIs.ite' (cF sCONT _ (by decide) rfl) (kSub Model.Sub.PLAIN) kNone)
        (UIs.chain_cons (cSub Model.Sub.C2) (UIs.ite' (cF sCONT _ (by decide) rfl) (kSub Model.Sub.C1) kNone)
        (UIs.chain_cons (cSub Model.Sub.C3) (UIs.ite' (cF sCONT _ (by decide) rfl) (kSub Model.Sub.C2) kNone)
        (UIs.chain_cons (cSub Model.Sub.E0s) (UIs.ite' (cF sA0BF _ (by decide) rfl) (kSub Model.Sub.C1) kNone)
        (UIs.chain_cons (cSub Model.Sub.EDs) (UIs.ite' (cF s809F _ (by decide) rfl) (kSub Model.Sub.C1) kNone)
        (UIs.chain_cons (cSub Model.Sub.F0s) (UIs.ite' (cF s90BF _ (by decide) rfl) (kSub Model.Sub.C2) kNone)
        (UIs.chain_nil (UIs.ite' (cF s808F _ (by decide) rfl) (kSub Model.Sub.C2) kNone))))))))))))))).congr ?_
    simp only [subnOf, Model.stepSub, subCode_ite, subCode_some, subCode_none,
      decide_eq_true_eq, beq_iff_eq]
  have v27 : UIs (blockCtx env L (blockVal r b active) 27)
      (kindE (reg i rCLAIM)) (kindOfCode r.claim) := by
    have h := uis_foldr_pred (ctx := blockCtx env L (blockVal r b active) 27)
      (fun k : Model.Claim => eqn (reg i rCLAIM) k.val)
      (fun k => decide (claimCode r.claim = k.val))
      (fun k => eval_eqn (gCLAIM 27)
        (by have := k.isLt; simp only [Model.nClaims] at this; omega))
      kindCode (fun k => by simp only [kindCode]; split_ifs <;> norm_num) 3 (by norm_num)
      (List.finRange nClaims)
    rw [find?_finRange_claimCode] at h
    exact h
  have v28 : UIs (blockCtx env L (blockVal r b active) 28)
      (U64Expr.ite (eqn (sigl i sWS) 1) (cst Model.St.AVAL.val)
        (U64Expr.ite (eqn (sigl i sB) comma) (cst Model.St.SEP.val)
          (U64Expr.ite (eqn (sigl i sB) rbrace) (cst Model.St.END.val) (cst stNone))))
      (stCode (Model.afterValue b)) := by
    refine (UIs.ite' (fS 28 sWS _ (by decide) rfl) (UIs.cst (hStLt _))
      (UIs.ite' (eB 28 _ (by norm_num) (by norm_num [Specs.JSON.comma])) (UIs.cst (hStLt _))
        (UIs.ite' (eB 28 _ (by norm_num) (by norm_num [Specs.JSON.rbrace])) (UIs.cst (hStLt _))
          (UIs.cst (by norm_num [stNone, Model.nSt]))))).congr ?_
    simp only [Model.afterValue, stCode_ite, stCode_some, stCode_none, decide_eq_true_eq,
      beq_iff_eq]
  have kSt : ∀ s : Model.St, UIs (blockCtx env L (blockVal r b active) 29) (cst s.val) s.val :=
    fun s => UIs.cst (hStLt s)
  have kStNone : UIs (blockCtx env L (blockVal r b active) 29) (cst stNone) stNone :=
    UIs.cst (by norm_num [stNone, Model.nSt])
  have gKIND : UIs (blockCtx env L (blockVal r b active) 29) (sigl i sKIND) (kindOfCode r.claim) :=
    gS 29 27 (by decide) (kindOfCode_lt _)
  have gAFT : UIs (blockCtx env L (blockVal r b active) 29) (sigl i sAFTERVAL) (stCode (Model.afterValue b)) :=
    gS 29 28 (by decide) (stCode_lt _)
  have cByte : ∀ n : ℕ, n < 2 ^ 64 →
      Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 29) (eqn (sigl i sB) n) = decide (b = n) :=
    fun n hn => eB 29 n (by norm_num) hn
  have cF : ∀ (m : ℕ) (c : Bool), m < 29 → blockVal r b active m = ub c →
      Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 29) (eqn (sigl i m) 1) = c :=
    fun m c hm hv => fS 29 m c hm hv
  have kStr : Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 29) (bor (eqn (sigl i sKIND) 0) (eqn (sigl i sKIND) 3))
      = (decide (Model.kindOf r.claim = .str) || decide (Model.kindOf r.claim = .unk)) := by
    rw [eval_bor, eval_eqn gKIND (by norm_num), eval_eqn gKIND (by norm_num), kindOfCode_str,
      kindOfCode_unk]
  have kInt : Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 29) (bor (eqn (sigl i sKIND) 1) (eqn (sigl i sKIND) 3))
      = (decide (Model.kindOf r.claim = .int) || decide (Model.kindOf r.claim = .unk)) := by
    rw [eval_bor, eval_eqn gKIND (by norm_num), eval_eqn gKIND (by norm_num), kindOfCode_int,
      kindOfCode_unk]
  have kBool : Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 29) (bor (eqn (sigl i sKIND) 2) (eqn (sigl i sKIND) 3))
      = (decide (Model.kindOf r.claim = .bool) || decide (Model.kindOf r.claim = .unk)) := by
    rw [eval_bor, eval_eqn gKIND (by norm_num), eval_eqn gKIND (by norm_num), kindOfCode_bool,
      kindOfCode_unk]
  have kUnkE : Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 29) (eqn (sigl i sKIND) 3) = decide (Model.kindOf r.claim = .unk) := by
    rw [eval_eqn gKIND (by norm_num), kindOfCode_unk]
  have v29 : UIs (blockCtx env L (blockVal r b active) 29)
      (chain [(eqn (reg i rST) Model.St.PRE.val, chain [(eqn (sigl i sWS) 1, cst Model.St.PRE.val), (eqn (sigl i sB) lbrace, cst Model.St.OBJ.val)] (cst stNone)),
          (eqn (reg i rST) Model.St.OBJ.val, chain [(eqn (sigl i sWS) 1, cst Model.St.OBJ.val), (eqn (sigl i sB) quote, cst Model.St.KEY.val), (eqn (sigl i sB) rbrace, cst Model.St.END.val)] (cst stNone)),
          (eqn (reg i rST) Model.St.KEY.val, U64Expr.ite (BExpr.and (eqn (sigl i sB) quote) (eqn (reg i rSUB) Model.Sub.PLAIN.val)) (cst Model.St.AKEY.val) (cst Model.St.KEY.val)),
          (eqn (reg i rST) Model.St.AKEY.val, chain [(eqn (sigl i sWS) 1, cst Model.St.AKEY.val), (eqn (sigl i sB) colon, cst Model.St.PVAL.val)] (cst stNone)),
          (eqn (reg i rST) Model.St.PVAL.val, chain [(eqn (sigl i sWS) 1, cst Model.St.PVAL.val), (BExpr.and (eqn (sigl i sB) quote) (bor (eqn (sigl i sKIND) 0) (eqn (sigl i sKIND) 3)), cst Model.St.STR.val), (BExpr.and (eqn (sigl i sB) minus) (bor (eqn (sigl i sKIND) 1) (eqn (sigl i sKIND) 3)), cst Model.St.NSIGN.val), (BExpr.and (eqn (sigl i sB) digit0) (bor (eqn (sigl i sKIND) 1) (eqn (sigl i sKIND) 3)), cst Model.St.NZERO.val), (BExpr.and (eqn (sigl i sDIGITNZ) 1) (bor (eqn (sigl i sKIND) 1) (eqn (sigl i sKIND) 3)), cst Model.St.NINT.val), (BExpr.and (eqn (sigl i sB) lowerT) (bor (eqn (sigl i sKIND) 2) (eqn (sigl i sKIND) 3)), cst Model.St.T1.val), (BExpr.and (eqn (sigl i sB) lowerF) (bor (eqn (sigl i sKIND) 2) (eqn (sigl i sKIND) 3)), cst Model.St.F1.val), (BExpr.and (eqn (sigl i sB) lowerN) (eqn (sigl i sKIND) 3), cst Model.St.N1.val)] (cst stNone)),
          (eqn (reg i rST) Model.St.STR.val, U64Expr.ite (BExpr.and (eqn (sigl i sB) quote) (eqn (reg i rSUB) Model.Sub.PLAIN.val)) (cst Model.St.AVAL.val) (cst Model.St.STR.val)),
          (eqn (reg i rST) Model.St.NSIGN.val, chain [(eqn (sigl i sB) digit0, cst Model.St.NZERO.val), (eqn (sigl i sDIGITNZ) 1, cst Model.St.NINT.val)] (cst stNone)),
          (eqn (reg i rST) Model.St.NZERO.val, chain [(BExpr.and (eqn (sigl i sB) dot) (eqn (sigl i sKIND) 3), cst Model.St.NDOT.val), (BExpr.and (eqn (sigl i sEXPL) 1) (eqn (sigl i sKIND) 3), cst Model.St.NE.val)] (sigl i sAFTERVAL)),
          (eqn (reg i rST) Model.St.NINT.val, chain [(eqn (sigl i sDIGIT) 1, cst Model.St.NINT.val), (BExpr.and (eqn (sigl i sB) dot) (eqn (sigl i sKIND) 3), cst Model.St.NDOT.val), (BExpr.and (eqn (sigl i sEXPL) 1) (eqn (sigl i sKIND) 3), cst Model.St.NE.val)] (sigl i sAFTERVAL)),
          (eqn (reg i rST) Model.St.NDOT.val, U64Expr.ite (eqn (sigl i sDIGIT) 1) (cst Model.St.NFRAC.val) (cst stNone)),
          (eqn (reg i rST) Model.St.NFRAC.val, chain [(eqn (sigl i sDIGIT) 1, cst Model.St.NFRAC.val), (eqn (sigl i sEXPL) 1, cst Model.St.NE.val)] (sigl i sAFTERVAL)),
          (eqn (reg i rST) Model.St.NE.val, chain [(eqn (sigl i sSIGN) 1, cst Model.St.NESIGN.val), (eqn (sigl i sDIGIT) 1, cst Model.St.NEXP.val)] (cst stNone)),
          (eqn (reg i rST) Model.St.NESIGN.val, U64Expr.ite (eqn (sigl i sDIGIT) 1) (cst Model.St.NEXP.val) (cst stNone)),
          (eqn (reg i rST) Model.St.NEXP.val, U64Expr.ite (eqn (sigl i sDIGIT) 1) (cst Model.St.NEXP.val) (sigl i sAFTERVAL)),
          (eqn (reg i rST) Model.St.T1.val, U64Expr.ite (eqn (sigl i sB) lowerR) (cst Model.St.T2.val) (cst stNone)),
          (eqn (reg i rST) Model.St.T2.val, U64Expr.ite (eqn (sigl i sB) lowerU) (cst Model.St.T3.val) (cst stNone)),
          (eqn (reg i rST) Model.St.T3.val, U64Expr.ite (eqn (sigl i sB) lowerE) (cst Model.St.AVAL.val) (cst stNone)),
          (eqn (reg i rST) Model.St.F1.val, U64Expr.ite (eqn (sigl i sB) lowerA) (cst Model.St.F2.val) (cst stNone)),
          (eqn (reg i rST) Model.St.F2.val, U64Expr.ite (eqn (sigl i sB) 0x6C) (cst Model.St.F3.val) (cst stNone)),
          (eqn (reg i rST) Model.St.F3.val, U64Expr.ite (eqn (sigl i sB) 0x73) (cst Model.St.F4.val) (cst stNone)),
          (eqn (reg i rST) Model.St.F4.val, U64Expr.ite (eqn (sigl i sB) lowerE) (cst Model.St.AVAL.val) (cst stNone)),
          (eqn (reg i rST) Model.St.N1.val, U64Expr.ite (eqn (sigl i sB) lowerU) (cst Model.St.N2.val) (cst stNone)),
          (eqn (reg i rST) Model.St.N2.val, U64Expr.ite (eqn (sigl i sB) 0x6C) (cst Model.St.N3.val) (cst stNone)),
          (eqn (reg i rST) Model.St.N3.val, U64Expr.ite (eqn (sigl i sB) 0x6C) (cst Model.St.AVAL.val) (cst stNone)),
          (eqn (reg i rST) Model.St.AVAL.val, sigl i sAFTERVAL),
          (eqn (reg i rST) Model.St.SEP.val, chain [(eqn (sigl i sWS) 1, cst Model.St.SEP.val), (eqn (sigl i sB) quote, cst Model.St.KEY.val)] (cst stNone))]
        (U64Expr.ite (eqn (sigl i sWS) 1) (cst Model.St.END.val) (cst stNone)))
      (stnOf r b) := by
    refine (UIs.chain_cons (eST 29 Model.St.PRE) (UIs.chain_cons (cF sWS _ (by decide) rfl) (kSt Model.St.PRE) (UIs.chain_cons (cByte _ ((by norm_num [Specs.JSON.lbrace]))) (kSt Model.St.OBJ) (UIs.chain_nil kStNone)))
        (UIs.chain_cons (eST 29 Model.St.OBJ) (UIs.chain_cons (cF sWS _ (by decide) rfl) (kSt Model.St.OBJ) (UIs.chain_cons (cByte _ ((by norm_num [Specs.JSON.quote]))) (kSt Model.St.KEY) (UIs.chain_cons (cByte _ ((by norm_num [Specs.JSON.rbrace]))) (kSt Model.St.END) (UIs.chain_nil kStNone))))
        (UIs.chain_cons (eST 29 Model.St.KEY) (UIs.ite' (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.quote]), eSUB 29 Model.Sub.PLAIN]) (kSt Model.St.AKEY) (kSt Model.St.KEY))
        (UIs.chain_cons (eST 29 Model.St.AKEY) (UIs.chain_cons (cF sWS _ (by decide) rfl) (kSt Model.St.AKEY) (UIs.chain_cons (cByte _ ((by norm_num [Specs.JSON.colon]))) (kSt Model.St.PVAL) (UIs.chain_nil kStNone)))
        (UIs.chain_cons (eST 29 Model.St.PVAL) (UIs.chain_cons (cF sWS _ (by decide) rfl) (kSt Model.St.PVAL) (UIs.chain_cons (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.quote]), kStr]) (kSt Model.St.STR) (UIs.chain_cons (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.minus]), kInt]) (kSt Model.St.NSIGN) (UIs.chain_cons (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.digit0]), kInt]) (kSt Model.St.NZERO) (UIs.chain_cons (by rw [eval_and, cF sDIGITNZ _ (by decide) rfl, kInt]) (kSt Model.St.NINT) (UIs.chain_cons (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.lowerT]), kBool]) (kSt Model.St.T1) (UIs.chain_cons (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.lowerF]), kBool]) (kSt Model.St.F1) (UIs.chain_cons (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.lowerN]), kUnkE]) (kSt Model.St.N1) (UIs.chain_nil kStNone)))))))))
        (UIs.chain_cons (eST 29 Model.St.STR) (UIs.ite' (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.quote]), eSUB 29 Model.Sub.PLAIN]) (kSt Model.St.AVAL) (kSt Model.St.STR))
        (UIs.chain_cons (eST 29 Model.St.NSIGN) (UIs.chain_cons (cByte _ ((by norm_num [Specs.JSON.digit0]))) (kSt Model.St.NZERO) (UIs.chain_cons (cF sDIGITNZ _ (by decide) rfl) (kSt Model.St.NINT) (UIs.chain_nil kStNone)))
        (UIs.chain_cons (eST 29 Model.St.NZERO) (UIs.chain_cons (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.dot]), kUnkE]) (kSt Model.St.NDOT) (UIs.chain_cons (by rw [eval_and, cF sEXPL _ (by decide) rfl, kUnkE]) (kSt Model.St.NE) (UIs.chain_nil gAFT)))
        (UIs.chain_cons (eST 29 Model.St.NINT) (UIs.chain_cons (cF sDIGIT _ (by decide) rfl) (kSt Model.St.NINT) (UIs.chain_cons (by rw [eval_and, cByte _ (by norm_num [Specs.JSON.dot]), kUnkE]) (kSt Model.St.NDOT) (UIs.chain_cons (by rw [eval_and, cF sEXPL _ (by decide) rfl, kUnkE]) (kSt Model.St.NE) (UIs.chain_nil gAFT))))
        (UIs.chain_cons (eST 29 Model.St.NDOT) (UIs.ite' (cF sDIGIT _ (by decide) rfl) (kSt Model.St.NFRAC) kStNone)
        (UIs.chain_cons (eST 29 Model.St.NFRAC) (UIs.chain_cons (cF sDIGIT _ (by decide) rfl) (kSt Model.St.NFRAC) (UIs.chain_cons (cF sEXPL _ (by decide) rfl) (kSt Model.St.NE) (UIs.chain_nil gAFT)))
        (UIs.chain_cons (eST 29 Model.St.NE) (UIs.chain_cons (cF sSIGN _ (by decide) rfl) (kSt Model.St.NESIGN) (UIs.chain_cons (cF sDIGIT _ (by decide) rfl) (kSt Model.St.NEXP) (UIs.chain_nil kStNone)))
        (UIs.chain_cons (eST 29 Model.St.NESIGN) (UIs.ite' (cF sDIGIT _ (by decide) rfl) (kSt Model.St.NEXP) kStNone)
        (UIs.chain_cons (eST 29 Model.St.NEXP) (UIs.ite' (cF sDIGIT _ (by decide) rfl) (kSt Model.St.NEXP) gAFT)
        (UIs.chain_cons (eST 29 Model.St.T1) (UIs.ite' (cByte _ ((by norm_num [Specs.JSON.lowerR]))) (kSt Model.St.T2) kStNone)
        (UIs.chain_cons (eST 29 Model.St.T2) (UIs.ite' (cByte _ ((by norm_num [Specs.JSON.lowerU]))) (kSt Model.St.T3) kStNone)
        (UIs.chain_cons (eST 29 Model.St.T3) (UIs.ite' (cByte _ ((by norm_num [Specs.JSON.lowerE]))) (kSt Model.St.AVAL) kStNone)
        (UIs.chain_cons (eST 29 Model.St.F1) (UIs.ite' (cByte _ ((by norm_num [Specs.JSON.lowerA]))) (kSt Model.St.F2) kStNone)
        (UIs.chain_cons (eST 29 Model.St.F2) (UIs.ite' (cByte _ ((by norm_num))) (kSt Model.St.F3) kStNone)
        (UIs.chain_cons (eST 29 Model.St.F3) (UIs.ite' (cByte _ ((by norm_num))) (kSt Model.St.F4) kStNone)
        (UIs.chain_cons (eST 29 Model.St.F4) (UIs.ite' (cByte _ ((by norm_num [Specs.JSON.lowerE]))) (kSt Model.St.AVAL) kStNone)
        (UIs.chain_cons (eST 29 Model.St.N1) (UIs.ite' (cByte _ ((by norm_num [Specs.JSON.lowerU]))) (kSt Model.St.N2) kStNone)
        (UIs.chain_cons (eST 29 Model.St.N2) (UIs.ite' (cByte _ ((by norm_num))) (kSt Model.St.N3) kStNone)
        (UIs.chain_cons (eST 29 Model.St.N3) (UIs.ite' (cByte _ ((by norm_num))) (kSt Model.St.AVAL) kStNone)
        (UIs.chain_cons (eST 29 Model.St.AVAL) gAFT
        (UIs.chain_cons (eST 29 Model.St.SEP) (UIs.chain_cons (cF sWS _ (by decide) rfl) (kSt Model.St.SEP) (UIs.chain_cons (cByte _ ((by norm_num [Specs.JSON.quote]))) (kSt Model.St.KEY) (UIs.chain_nil kStNone)))
        (UIs.chain_nil (UIs.ite' (cF sWS _ (by decide) rfl) (kSt Model.St.END) kStNone)))))))))))))))))))))))))))).congr ?_
    simp only [stnOf, Model.stepSt, stCode_ite, stCode_some, stCode_none,
      decide_eq_true_eq, beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true]
  have gCP : ∀ k, 25 < k → UIs (blockCtx env L (blockVal r b active) k) (sigl i sCP) ((sigOf r b).cp) :=
    fun k hk => gS k 25 hk (by
      have := sigOf_cp_lt hb hhex
      simp only [blockVal]; omega)
  have gSUBN : ∀ k, 26 < k →
      UIs (blockCtx env L (blockVal r b active) k) (sigl i sSUBN) (subnOf r b) :=
    fun k hk => gS k 26 hk (subCode_lt _)
  have gKINDs : ∀ k, 27 < k →
      UIs (blockCtx env L (blockVal r b active) k) (sigl i sKIND) (kindOfCode r.claim) :=
    fun k hk => gS k 27 hk (kindOfCode_lt _)
  have gSTN : ∀ k, 29 < k →
      UIs (blockCtx env L (blockVal r b active) k) (sigl i sSTN) (stnOf r b) :=
    fun k hk => gS k 29 hk (stCode_lt _)
  have gMIDX : ∀ k, 32 < k →
      UIs (blockCtx env L (blockVal r b active) k) (sigl i sMATCHIDX) (matchIdxOf r b) :=
    fun k hk => gS k 32 hk (matchIdxOf_lt r b)
  have v30 : UIs (blockCtx env L (blockVal r b active) 30)
      (toU (BExpr.and (eqn (sigl i sSTN) Model.St.KEY.val)
        (BExpr.not (eqn (reg i rST) Model.St.KEY.val))))
      (ub (sigOf r b).keyStart) :=
    UIs.toU' (by
      rw [eval_and, eval_not, eval_eqn (gSTN 30 (by norm_num)) (hStLt _),
        eST 30 Model.St.KEY, eq_keyStart])
  have v31 : UIs (blockCtx env L (blockVal r b active) 31)
      (toU (BExpr.and (BExpr.and (eqn (reg i rST) Model.St.KEY.val) (eqn (sigl i sB) quote))
        (eqn (reg i rSUB) Model.Sub.PLAIN.val)))
      (ub (sigOf r b).keyClose) :=
    UIs.toU' (by
      rw [eval_and, eval_and, eST 31 Model.St.KEY,
        eB 31 _ (by norm_num) (by norm_num [Specs.JSON.quote]), eSUB 31 Model.Sub.PLAIN,
        sigOf_keyClose, beq_eq_decide])
  have v32 : UIs (blockCtx env L (blockVal r b active) 32)
      ((List.finRange nClaims).foldr
        (fun k acc => U64Expr.ite (BExpr.and (eqn (sigl i sKEYCLOSE) 1)
          (BExpr.and (eqn (reg i (rM + k.val)) 1)
            (eqn (reg i rKIDX) (Model.claimName k).length))) (cst k.val) acc)
        (cst claimNone))
      (matchIdxOf r b) := by
    refine uis_foldr_pred _ (fun k => (sigOf r b).match_[k]) (fun k => ?_) (fun k => k.val)
      (fun k => by have := k.isLt; simp only [Model.nClaims] at this; omega) claimNone
      (by norm_num [claimNone, Model.nClaims]) (List.finRange nClaims)
    rw [eval_and, eval_and, fS 32 sKEYCLOSE _ (by decide) rfl,
      eval_flagN (gM 32 k.val k.isLt),
      eval_eqn (gKIDX 32) (by
        have := Model.claimName_length_lt k
        simp only [Model.kIdxMax] at this; omega),
      sigOf_match, Bool.and_assoc]
    rfl
  have v33 : UIs (blockCtx env L (blockVal r b active) 33)
      (toU (BExpr.and (eqn (sigl i sEMIT) 1) (eqn (reg i rST) Model.St.STR.val)))
      (ub ((sigOf r b).emit && decide (r.st = Model.St.STR))) :=
    UIs.toU' (by rw [eval_and, fS 33 sEMIT _ (by decide) rfl, eST 33 Model.St.STR])
  have v34 : UIs (blockCtx env L (blockVal r b active) 34)
      (toU (BExpr.and (eqn (sigl i sDIGIT) 1)
        (bor (eqn (reg i rST) Model.St.PVAL.val)
          (bor (eqn (reg i rST) Model.St.NSIGN.val) (eqn (reg i rST) Model.St.NINT.val)))))
      (ub (sigOf r b).digitEmit) :=
    UIs.toU' (by
      rw [eval_and, eval_bor, eval_bor, fS 34 sDIGIT _ (by decide) rfl,
        eST 34 Model.St.PVAL, eST 34 Model.St.NSIGN, eST 34 Model.St.NINT, sigOf_digitEmit,
        Bool.or_assoc])
  have v35 : UIs (blockCtx env L (blockVal r b active) 35)
      (toU (bor (eqn (sigl i sSTREMIT) 1) (eqn (sigl i sDIGITEMIT) 1)))
      (ub (sigOf r b).vEmit) :=
    UIs.toU' (by
      rw [eval_bor, fS 35 sSTREMIT _ (by decide) rfl, fS 35 sDIGITEMIT _ (by decide) rfl,
        sigOf_vEmit])
  have v36 : UIs (blockCtx env L (blockVal r b active) 36)
      (toU (BExpr.and (eqn (sigl i sVEMIT) 1)
        (bor (eqn (sigl i sKIND) 0) (eqn (sigl i sKIND) 1))))
      (ub (sigOf r b).write) :=
    UIs.toU' (by
      rw [eval_and, eval_bor, fS 36 sVEMIT _ (by decide) rfl,
        eval_eqn (gKINDs 36 (by norm_num)) (by norm_num),
        eval_eqn (gKINDs 36 (by norm_num)) (by norm_num),
        kindOfCode_str, kindOfCode_int, sigOf_write])
  have v37 : UIs (blockCtx env L (blockVal r b active) 37)
      (U64Expr.ite (eqn (sigl i sSTREMIT) 1) (sigl i sCP)
        (U64Expr.ite (eqn (sigl i sDIGITEMIT) 1) (subN (sigl i sB) digit0) (cst 0)))
      ((sigOf r b).valOut) := by
    rw [sigOf_valOut]
    by_cases h1 : ((sigOf r b).emit && decide (r.st = Model.St.STR)) = true
    · rw [if_pos h1]
      exact UIs.ite_pos (by rw [fS 37 sSTREMIT _ (by decide) rfl]; exact h1) (gCP 37 (by norm_num))
    · rw [if_neg h1]
      refine UIs.ite_neg (by
        rw [fS 37 sSTREMIT _ (by decide) rfl]; simpa using h1) ?_
      by_cases h2 : (sigOf r b).digitEmit = true
      · rw [if_pos h2]
        exact UIs.ite_pos (by rw [fS 37 sDIGITEMIT _ (by decide) rfl]; exact h2)
          (UIs.subN (gBS 37 (by norm_num)) (digit0_le_of_digitEmit h2))
      · rw [if_neg h2]
        exact UIs.ite_neg (by rw [fS 37 sDIGITEMIT _ (by decide) rfl]; simpa using h2)
          (UIs.cst (by norm_num))
  have v38 : UIs (blockCtx env L (blockVal r b active) 38)
      (toU (BExpr.and (eqn (reg i rST) Model.St.PVAL.val) (eqn (sigl i sB) minus)))
      (ub (sigOf r b).minusFlag) :=
    UIs.toU' (by
      rw [eval_and, eST 38 Model.St.PVAL,
        eB 38 _ (by norm_num) (by norm_num [Specs.JSON.minus]), sigOf_minusFlag, beq_eq_decide])
  have v39 : UIs (blockCtx env L (blockVal r b active) 39)
      (toU (BExpr.and (eqn (reg i rST) Model.St.T3.val) (eqn (sigl i sB) lowerE)))
      (ub (sigOf r b).trueDone) :=
    UIs.toU' (by
      rw [eval_and, eST 39 Model.St.T3,
        eB 39 _ (by norm_num) (by norm_num [Specs.JSON.lowerE]), sigOf_trueDone, beq_eq_decide])
  have vcap : UIs (blockCtx env L (blockVal r b active) 40) (capE (reg i rCLAIM)) (capOf r.claim) := by
    have h := uis_foldr_pred (ctx := (blockCtx env L (blockVal r b active) 40))
      (fun k : Model.Claim => eqn (reg i rCLAIM) k.val)
      (fun k => decide (claimCode r.claim = k.val))
      (fun k => eval_eqn (gCLAIM 40)
        (by have := k.isLt; simp only [Model.nClaims] at this; omega))
      Model.claimCap claimCap_lt 0 (by norm_num) (List.finRange nClaims)
    rw [find?_finRange_claimCode] at h
    exact h
  have v40 : UIs (blockCtx env L (blockVal r b active) 40)
      (toU (BExpr.and
        (BExpr.and (BExpr.not (eqn (sigl i sSUBN) subNone))
          (BExpr.not (eqn (sigl i sSTN) stNone)))
        (BExpr.and
          (bor (BExpr.not (eqn (sigl i sWRITE) 1))
            (bor (eqn (reg i rCLAIM) claimNone)
              (BExpr.lt (reg i rOFS) (capE (reg i rCLAIM)))))
          (bor (BExpr.not (BExpr.and (eqn (sigl i sWRITE) 1)
              (eqn (reg i rST) Model.St.STR.val)))
            (BExpr.lt (sigl i sCP) (cst 0x80))))))
      (ub (Model.step r b).isSome) :=
    UIs.toU' (by
      simp only [eval_and, eval_not, eval_bor]
      rw [eval_eqn (gSUBN 40 (by norm_num)) (by norm_num [subNone, Model.nSub]),
        eval_eqn (gSTN 40 (by norm_num)) (by norm_num [stNone, Model.nSt]),
        fS 40 sWRITE _ (by decide) rfl,
        eval_eqn (gCLAIM 40) (by norm_num [claimNone, Model.nClaims]),
        eval_ltU (gOFS 40) vcap, eST 40 Model.St.STR,
        eval_ltU (gCP 40 (by norm_num)) (UIs.cst (by norm_num)), step_isSome_eq])
  have v41 : UIs (blockCtx env L (blockVal r b active) 41)
      (toU (BExpr.and (eqn (sigl i sACTIVE) 1) (eqn (sigl i sOK) 1)))
      (ub (active && (Model.step r b).isSome)) :=
    UIs.toU' (by rw [eval_and, fS 41 sACTIVE _ (by decide) rfl, fS 41 sOK _ (by decide) rfl])
  have v42 : UIs (blockCtx env L (blockVal r b active) 42)
      (U64Expr.ite (BExpr.and (eqn (sigl i sACTIVE) 1) (eqn (sigl i sWRITE) 1))
        (U64Expr.add (U64Expr.mul (reg i rCLAIM) (cst ofsMax)) (reg i rOFS)) (cst cellNone))
      (if active && (sigOf r b).write then claimCode r.claim * ofsMax + r.ofs else cellNone) :=
    UIs.ite' (by rw [eval_and, fS 42 sACTIVE _ (by decide) rfl, fS 42 sWRITE _ (by decide) rfl])
      (UIs.add (UIs.mul (gCLAIM 42) (UIs.cst (by norm_num [Model.ofsMax]))
          (by
            have : claimCode r.claim ≤ nClaims := by
              cases hc : r.claim with
              | none => simp [claimCode, hc, claimNone]
              | some k => have := k.isLt; simp only [claimCode, hc, Option.elim]; omega
            simp only [Model.nClaims] at this
            simp only [Model.ofsMax]; omega))
        (gOFS 42)
        (by
          have h1 : claimCode r.claim ≤ nClaims := by
            cases hc : r.claim with
            | none => simp [claimCode, hc, claimNone]
            | some k => have := k.isLt; simp only [claimCode, hc, Option.elim]; omega
          simp only [Model.nClaims] at h1
          simp only [Model.ofsMax] at hofs ⊢; omega))
      (UIs.cst (by norm_num [cellNone, Model.nClaims, Model.ofsMax]))
  have v43 : UIs (blockCtx env L (blockVal r b active) 43)
      (U64Expr.ite (eqn (sigl i sACTIVE) 1) (sigl i sMATCHIDX) (cst claimNone))
      (if active then matchIdxOf r b else claimNone) :=
    UIs.ite' (fS 43 sACTIVE _ (by decide) rfl) (gMIDX 43 (by norm_num))
      (UIs.cst (by norm_num [claimNone, Model.nClaims]))
  have v44 : UIs (blockCtx env L (blockVal r b active) 44)
      (U64Expr.ite (BExpr.and (eqn (sigl i sACTIVE) 1) (eqn (sigl i sVEMIT) 1)) (reg i rCLAIM)
        (cst claimNone))
      (if active && (sigOf r b).vEmit then claimCode r.claim else claimNone) :=
    UIs.ite' (by rw [eval_and, fS 44 sACTIVE _ (by decide) rfl, fS 44 sVEMIT _ (by decide) rfl])
      (gCLAIM 44) (UIs.cst (by norm_num [claimNone, Model.nClaims]))
  have v45 : UIs (blockCtx env L (blockVal r b active) 45)
      (U64Expr.ite (BExpr.and (eqn (sigl i sACTIVE) 1) (eqn (sigl i sMINUS) 1)) (reg i rCLAIM)
        (cst claimNone))
      (if active && (sigOf r b).minusFlag then claimCode r.claim else claimNone) :=
    UIs.ite' (by rw [eval_and, fS 45 sACTIVE _ (by decide) rfl, fS 45 sMINUS _ (by decide) rfl])
      (gCLAIM 45) (UIs.cst (by norm_num [claimNone, Model.nClaims]))
  have v46 : UIs (blockCtx env L (blockVal r b active) 46)
      (U64Expr.ite (BExpr.and (eqn (sigl i sACTIVE) 1) (eqn (sigl i sTRUEDONE) 1)) (reg i rCLAIM)
        (cst claimNone))
      (if active && (sigOf r b).trueDone then claimCode r.claim else claimNone) :=
    UIs.ite' (by rw [eval_and, fS 46 sACTIVE _ (by decide) rfl, fS 46 sTRUEDONE _ (by decide) rfl])
      (gCLAIM 46) (UIs.cst (by norm_num [claimNone, Model.nClaims]))
  have hADV : ∀ k, 41 < k →
      Witgen.BExpr.eval (blockCtx env L (blockVal r b active) k) (eqn (sigl i sADV) 1)
        = (active && (Model.step r b).isSome) := fun k hk => fS k sADV _ hk rfl
  have uEMIT : ∀ k, 23 < k →
      UIs (blockCtx env L (blockVal r b active) k) (sigl i sEMIT) (ub (sigOf r b).emit) :=
    fun k hk => gS k 23 hk (ub_lt _)
  have uVEMIT : ∀ k, 35 < k →
      UIs (blockCtx env L (blockVal r b active) k) (sigl i sVEMIT) (ub (sigOf r b).vEmit) :=
    fun k hk => gS k 35 hk (ub_lt _)
  have uKEYSTART : ∀ k, 30 < k →
      UIs (blockCtx env L (blockVal r b active) k) (sigl i sKEYSTART)
        (ub (sigOf r b).keyStart) := fun k hk => gS k 30 hk (ub_lt _)
  have uHV : ∀ k, 24 < k →
      UIs (blockCtx env L (blockVal r b active) k) (sigl i sHV) (Model.hexVal b) :=
    fun k hk => gS k 24 hk (by have := hexVal_lt b; simp only [blockVal]; omega)
  have hkidx15 : r.kIdx ≤ 15 := by simp only [Model.kIdxMax] at hkidx; omega
  have hofs128 : r.ofs ≤ 128 := by simp only [Model.ofsMax] at hofs; omega
  have hnmem1024 : r.nMem ≤ 1024 := by simp only [bufferLen] at hnmem; omega
  have v47 : UIs (blockCtx env L (blockVal r b active) 47)
      (U64Expr.ite (eqn (sigl i sADV) 1) (sigl i sSTN) (reg i rST))
      ((nextRegs r b active).st.val) := by
    cases hadv : (active && (Model.step r b).isSome) with
    | false =>
        rw [nextRegs_of_not_adv hadv]
        exact UIs.ite_neg (by rw [hADV 47 (by norm_num)]; exact hadv) (gST 47)
    | true =>
        obtain ⟨hact2, hsome⟩ : active = true ∧ (Model.step r b).isSome = true := by
          simpa using hadv
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
        rw [nextRegs_of_adv hact2 hr']
        refine (UIs.ite_pos (by rw [hADV 47 (by norm_num)]; exact hadv)
          (gSTN 47 (by norm_num))).congr ?_
        exact (step_some_fields hr').1.symm
  have v48 : UIs (blockCtx env L (blockVal r b active) 48)
      (U64Expr.ite (eqn (sigl i sADV) 1) (sigl i sSUBN) (reg i rSUB))
      ((nextRegs r b active).sub.val) := by
    cases hadv : (active && (Model.step r b).isSome) with
    | false =>
        rw [nextRegs_of_not_adv hadv]
        exact UIs.ite_neg (by rw [hADV 48 (by norm_num)]; exact hadv) (gSUB 48)
    | true =>
        obtain ⟨hact2, hsome⟩ : active = true ∧ (Model.step r b).isSome = true := by
          simpa using hadv
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
        rw [nextRegs_of_adv hact2 hr']
        refine (UIs.ite_pos (by rw [hADV 48 (by norm_num)]; exact hadv)
          (gSUBN 48 (by norm_num))).congr ?_
        exact (step_some_fields hr').2.1.symm
  have v49 : UIs (blockCtx env L (blockVal r b active) 49)
      (U64Expr.ite (eqn (sigl i sADV) 1)
        (U64Expr.ite (bor (eqn (reg i rSUB) Model.Sub.H1.val)
            (bor (eqn (reg i rSUB) Model.Sub.H2.val) (eqn (reg i rSUB) Model.Sub.H3.val)))
          (U64Expr.add (U64Expr.mul (cst 16) (reg i rHEXACC)) (sigl i sHV)) (cst 0))
        (reg i rHEXACC))
      ((nextRegs r b active).hexAcc) := by
    have hinner : UIs (blockCtx env L (blockVal r b active) 49)
        (U64Expr.ite (bor (eqn (reg i rSUB) Model.Sub.H1.val)
            (bor (eqn (reg i rSUB) Model.Sub.H2.val) (eqn (reg i rSUB) Model.Sub.H3.val)))
          (U64Expr.add (U64Expr.mul (cst 16) (reg i rHEXACC)) (sigl i sHV)) (cst 0))
        (if (decide (r.sub = Model.Sub.H1) ||
            (decide (r.sub = Model.Sub.H2) || decide (r.sub = Model.Sub.H3)))
          then 16 * r.hexAcc + Model.hexVal b else 0) := by
      have hhv := hexVal_lt b
      exact UIs.ite' (by rw [eval_bor, eval_bor, eSUB 49 Model.Sub.H1, eSUB 49 Model.Sub.H2,
          eSUB 49 Model.Sub.H3])
        (UIs.add (UIs.mul (UIs.cst (by norm_num)) (gHEX 49) (by omega)) (uHV 49 (by norm_num))
          (by omega))
        (UIs.cst (by norm_num))
    cases hadv : (active && (Model.step r b).isSome) with
    | false =>
        rw [nextRegs_of_not_adv hadv]
        exact UIs.ite_neg (by rw [hADV 49 (by norm_num)]; exact hadv) (gHEX 49)
    | true =>
        obtain ⟨hact2, hsome⟩ : active = true ∧ (Model.step r b).isSome = true := by
          simpa using hadv
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
        rw [nextRegs_of_adv hact2 hr']
        refine (UIs.ite_pos (by rw [hADV 49 (by norm_num)]; exact hadv) hinner).congr ?_
        exact (step_some_fields hr').2.2.1.symm
  have v50 : UIs (blockCtx env L (blockVal r b active) 50)
      (U64Expr.ite (eqn (sigl i sADV) 1)
        (U64Expr.ite (eqn (reg i rST) Model.St.KEY.val)
          (minN (U64Expr.add (reg i rKIDX) (sigl i sEMIT)) (kIdxMax - 1)) (cst 0))
        (reg i rKIDX))
      ((nextRegs r b active).kIdx) := by
    have hinner : UIs (blockCtx env L (blockVal r b active) 50)
        (U64Expr.ite (eqn (reg i rST) Model.St.KEY.val)
          (minN (U64Expr.add (reg i rKIDX) (sigl i sEMIT)) (kIdxMax - 1)) (cst 0))
        (if r.st = Model.St.KEY then min (r.kIdx + ub (sigOf r b).emit) (kIdxMax - 1) else 0) := by
      refine (UIs.ite' (eST 50 Model.St.KEY)
        (UIs.minN (UIs.add (gKIDX 50) (uEMIT 50 (by norm_num))
          (by have := ub_le_one (sigOf r b).emit; omega)) (by norm_num [Model.kIdxMax]))
        (UIs.cst (n := 0) (by norm_num))).congr ?_
      simp
    cases hadv : (active && (Model.step r b).isSome) with
    | false =>
        rw [nextRegs_of_not_adv hadv]
        exact UIs.ite_neg (by rw [hADV 50 (by norm_num)]; exact hadv) (gKIDX 50)
    | true =>
        obtain ⟨hact2, hsome⟩ : active = true ∧ (Model.step r b).isSome = true := by
          simpa using hadv
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
        rw [nextRegs_of_adv hact2 hr']
        refine (UIs.ite_pos (by rw [hADV 50 (by norm_num)]; exact hadv) hinner).congr ?_
        exact (step_some_fields hr').2.2.2.1.symm
  have v51 : UIs (blockCtx env L (blockVal r b active) 51)
      (U64Expr.ite (eqn (sigl i sADV) 1)
        (U64Expr.ite (eqn (sigl i sKEYCLOSE) 1) (sigl i sMATCHIDX)
          (U64Expr.ite (eqn (sigl i sKEYSTART) 1) (cst claimNone) (reg i rCLAIM)))
        (reg i rCLAIM))
      (claimCode (nextRegs r b active).claim) := by
    have hinner : UIs (blockCtx env L (blockVal r b active) 51)
        (U64Expr.ite (eqn (sigl i sKEYCLOSE) 1) (sigl i sMATCHIDX)
          (U64Expr.ite (eqn (sigl i sKEYSTART) 1) (cst claimNone) (reg i rCLAIM)))
        (if (sigOf r b).keyClose then matchIdxOf r b
          else if (sigOf r b).keyStart then claimNone else claimCode r.claim) :=
      UIs.ite' (fS 51 sKEYCLOSE _ (by decide) rfl) (gMIDX 51 (by norm_num))
        (UIs.ite' (fS 51 sKEYSTART _ (by decide) rfl)
          (UIs.cst (by norm_num [claimNone, Model.nClaims])) (gCLAIM 51))
    cases hadv : (active && (Model.step r b).isSome) with
    | false =>
        rw [nextRegs_of_not_adv hadv]
        exact UIs.ite_neg (by rw [hADV 51 (by norm_num)]; exact hadv) (gCLAIM 51)
    | true =>
        obtain ⟨hact2, hsome⟩ : active = true ∧ (Model.step r b).isSome = true := by
          simpa using hadv
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
        rw [nextRegs_of_adv hact2 hr']
        refine (UIs.ite_pos (by rw [hADV 51 (by norm_num)]; exact hadv) hinner).congr ?_
        exact (step_some_fields hr').2.2.2.2.1.symm
  have v52 : UIs (blockCtx env L (blockVal r b active) 52)
      (U64Expr.ite (eqn (sigl i sADV) 1)
        (minN (U64Expr.add
          (U64Expr.ite (BExpr.not (anyEq (reg i rST)
            [Model.St.PRE.val, Model.St.OBJ.val, Model.St.KEY.val, Model.St.AKEY.val,
             Model.St.PVAL.val, Model.St.AVAL.val, Model.St.SEP.val, Model.St.END.val]))
            (reg i rOFS) (cst 0)) (sigl i sVEMIT)) (ofsMax - 1))
        (reg i rOFS))
      ((nextRegs r b active).ofs) := by
    have hcond : Witgen.BExpr.eval (blockCtx env L (blockVal r b active) 52)
        (BExpr.not (anyEq (reg i rST)
          [Model.St.PRE.val, Model.St.OBJ.val, Model.St.KEY.val, Model.St.AKEY.val,
           Model.St.PVAL.val, Model.St.AVAL.val, Model.St.SEP.val, Model.St.END.val]))
        = (decide (r.st ≠ Model.St.PRE) && decide (r.st ≠ Model.St.OBJ) &&
            decide (r.st ≠ Model.St.KEY) && decide (r.st ≠ Model.St.AKEY) &&
            decide (r.st ≠ Model.St.PVAL) && decide (r.st ≠ Model.St.AVAL) &&
            decide (r.st ≠ Model.St.SEP) && decide (r.st ≠ Model.St.END)) := by
      rw [eval_not, eval_anyEq (gST 52) _ (by
        intro n hn
        fin_cases hn <;> exact lt_trans (Fin.isLt _) nSt_lt64), anyEq_st_inVal, Bool.not_not]
    have hinner : UIs (blockCtx env L (blockVal r b active) 52)
        (minN (U64Expr.add
          (U64Expr.ite (BExpr.not (anyEq (reg i rST)
            [Model.St.PRE.val, Model.St.OBJ.val, Model.St.KEY.val, Model.St.AKEY.val,
             Model.St.PVAL.val, Model.St.AVAL.val, Model.St.SEP.val, Model.St.END.val]))
            (reg i rOFS) (cst 0)) (sigl i sVEMIT)) (ofsMax - 1))
        (min ((if (decide (r.st ≠ Model.St.PRE) && decide (r.st ≠ Model.St.OBJ) &&
            decide (r.st ≠ Model.St.KEY) && decide (r.st ≠ Model.St.AKEY) &&
            decide (r.st ≠ Model.St.PVAL) && decide (r.st ≠ Model.St.AVAL) &&
            decide (r.st ≠ Model.St.SEP) && decide (r.st ≠ Model.St.END)) then r.ofs else 0)
          + ub (sigOf r b).vEmit) (ofsMax - 1)) :=
      UIs.minN (UIs.add (UIs.ite' hcond (gOFS 52) (UIs.cst (by norm_num)))
        (uVEMIT 52 (by norm_num))
        (by have := ub_le_one (sigOf r b).vEmit; split_ifs <;> omega))
        (by norm_num [Model.ofsMax])
    cases hadv : (active && (Model.step r b).isSome) with
    | false =>
        rw [nextRegs_of_not_adv hadv]
        exact UIs.ite_neg (by rw [hADV 52 (by norm_num)]; exact hadv) (gOFS 52)
    | true =>
        obtain ⟨hact2, hsome⟩ : active = true ∧ (Model.step r b).isSome = true := by
          simpa using hadv
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
        rw [nextRegs_of_adv hact2 hr']
        refine (UIs.ite_pos (by rw [hADV 52 (by norm_num)]; exact hadv) hinner).congr ?_
        exact (step_some_fields hr').2.2.2.2.2.1.symm
  have v53 : UIs (blockCtx env L (blockVal r b active) 53)
      (U64Expr.ite (eqn (sigl i sADV) 1)
        (U64Expr.add (reg i rNMEM) (sigl i sKEYSTART)) (reg i rNMEM))
      ((nextRegs r b active).nMem) := by
    have hinner : UIs (blockCtx env L (blockVal r b active) 53)
        (U64Expr.add (reg i rNMEM) (sigl i sKEYSTART))
        (r.nMem + ub (sigOf r b).keyStart) :=
      UIs.add (gNMEM 53) (uKEYSTART 53 (by norm_num))
        (by have := ub_le_one (sigOf r b).keyStart; omega)
    cases hadv : (active && (Model.step r b).isSome) with
    | false =>
        rw [nextRegs_of_not_adv hadv]
        exact UIs.ite_neg (by rw [hADV 53 (by norm_num)]; exact hadv) (gNMEM 53)
    | true =>
        obtain ⟨hact2, hsome⟩ : active = true ∧ (Model.step r b).isSome = true := by
          simpa using hadv
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
        rw [nextRegs_of_adv hact2 hr']
        refine (UIs.ite_pos (by rw [hADV 53 (by norm_num)]; exact hadv) hinner).congr ?_
        exact (step_some_fields hr').2.2.2.2.2.2.1.symm
  have vM : ∀ k : Model.Claim, UIs (blockCtx env L (blockVal r b active) (54 + k.val))
      (U64Expr.ite (eqn (sigl i sADV) 1)
        (U64Expr.ite (eqn (sigl i sKEYSTART) 1) (cst 1)
          (U64Expr.ite (eqn (reg i rST) Model.St.KEY.val)
            (toU (BExpr.and (eqn (reg i (rM + k.val)) 1)
              (bor (BExpr.not (eqn (sigl i sEMIT) 1))
                (BExpr.neq (sigl i sCP) (nameAtE k (reg i rKIDX)))))) (cst 0)))
        (reg i (rM + k.val)))
      (ub ((nextRegs r b active).m[k.val]'k.isLt)) := by
    intro k
    have hinner : UIs (blockCtx env L (blockVal r b active) (54 + k.val))
        (U64Expr.ite (eqn (sigl i sKEYSTART) 1) (cst 1)
          (U64Expr.ite (eqn (reg i rST) Model.St.KEY.val)
            (toU (BExpr.and (eqn (reg i (rM + k.val)) 1)
              (bor (BExpr.not (eqn (sigl i sEMIT) 1))
                (BExpr.neq (sigl i sCP) (nameAtE k (reg i rKIDX)))))) (cst 0)))
        (ub (if (sigOf r b).keyStart then true
          else if r.st = Model.St.KEY then
            (r.m[k] && (!(sigOf r b).emit ||
              decide ((sigOf r b).cp = Model.nameAt k r.kIdx))) else false)) := by
      refine (UIs.ite' (fS (54 + k.val) sKEYSTART _ (by (try simp only [sKEYSTART]); omega) rfl)
        (UIs.cst (n := 1) (by norm_num))
        (UIs.ite' (eST (54 + k.val) Model.St.KEY)
          (UIs.toU' (by
            rw [eval_and, eval_bor, eval_not,
              eval_flagN (gM (54 + k.val) k.val k.isLt),
              fS (54 + k.val) sEMIT _ (by (try simp only [sEMIT]); omega) rfl,
              eval_neqU (gCP (54 + k.val) (by (try simp only [sCP]); omega))
                (uis_nameAtE (gKIDX (54 + k.val)) (by simp only [Model.kIdxMax]; omega) k)]))
          (UIs.cst (n := 0) (by norm_num)))).congr ?_
      simp only [ub]
      split_ifs <;> simp_all
    cases hadv : (active && (Model.step r b).isSome) with
    | false =>
        rw [nextRegs_of_not_adv hadv]
        exact UIs.ite_neg (by rw [hADV (54 + k.val) (by (try simp only [sADV]); omega)]; exact hadv)
          (gM (54 + k.val) k.val k.isLt)
    | true =>
        obtain ⟨hact2, hsome⟩ : active = true ∧ (Model.step r b).isSome = true := by
          simpa using hadv
        obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
        rw [nextRegs_of_adv hact2 hr']
        refine (UIs.ite_pos (by rw [hADV (54 + k.val) (by (try simp only [sADV]); omega)]; exact hadv)
          hinner).congr ?_
        exact congrArg ub ((step_some_fields hr').2.2.2.2.2.2.2 k).symm
  have h0 : evalSteps env (stepBlock input i) L
      = evalSteps env (stepBlock input i) (L ++ accOf (blockVal r b active) 0) := by
    simp [accOf]
  rw [h0]
  refine Eq.trans (step_accOf _ v0) ?_
  refine Eq.trans (step_accOf _ v1) ?_
  refine Eq.trans (step_accOf _ v2) ?_
  refine Eq.trans (step_accOf _ v3) ?_
  refine Eq.trans (step_accOf _ v4) ?_
  refine Eq.trans (step_accOf _ v5) ?_
  refine Eq.trans (step_accOf _ v6) ?_
  refine Eq.trans (step_accOf _ v7) ?_
  refine Eq.trans (step_accOf _ v8) ?_
  refine Eq.trans (step_accOf _ v9) ?_
  refine Eq.trans (step_accOf _ v10) ?_
  refine Eq.trans (step_accOf _ v11) ?_
  refine Eq.trans (step_accOf _ v12) ?_
  refine Eq.trans (step_accOf _ v13) ?_
  refine Eq.trans (step_accOf _ v14) ?_
  refine Eq.trans (step_accOf _ v15) ?_
  refine Eq.trans (step_accOf _ v16) ?_
  refine Eq.trans (step_accOf _ v17) ?_
  refine Eq.trans (step_accOf _ v18) ?_
  refine Eq.trans (step_accOf _ v19) ?_
  refine Eq.trans (step_accOf _ v20) ?_
  refine Eq.trans (step_accOf _ v21) ?_
  refine Eq.trans (step_accOf _ v22) ?_
  refine Eq.trans (step_accOf _ v23) ?_
  refine Eq.trans (step_accOf _ v24) ?_
  refine Eq.trans (step_accOf _ v25) ?_
  refine Eq.trans (step_accOf _ v26) ?_
  refine Eq.trans (step_accOf _ v27) ?_
  refine Eq.trans (step_accOf _ v28) ?_
  refine Eq.trans (step_accOf _ v29) ?_
  refine Eq.trans (step_accOf _ v30) ?_
  refine Eq.trans (step_accOf _ v31) ?_
  refine Eq.trans (step_accOf _ v32) ?_
  refine Eq.trans (step_accOf _ v33) ?_
  refine Eq.trans (step_accOf _ v34) ?_
  refine Eq.trans (step_accOf _ v35) ?_
  refine Eq.trans (step_accOf _ v36) ?_
  refine Eq.trans (step_accOf _ v37) ?_
  refine Eq.trans (step_accOf _ v38) ?_
  refine Eq.trans (step_accOf _ v39) ?_
  refine Eq.trans (step_accOf _ v40) ?_
  refine Eq.trans (step_accOf _ v41) ?_
  refine Eq.trans (step_accOf _ v42) ?_
  refine Eq.trans (step_accOf _ v43) ?_
  refine Eq.trans (step_accOf _ v44) ?_
  refine Eq.trans (step_accOf _ v45) ?_
  refine Eq.trans (step_accOf _ v46) ?_
  refine Eq.trans (step_accOf _ v47) ?_
  refine Eq.trans (step_accOf _ v48) ?_
  refine Eq.trans (step_accOf _ v49) ?_
  refine Eq.trans (step_accOf _ v50) ?_
  refine Eq.trans (step_accOf _ v51) ?_
  refine Eq.trans (step_accOf _ v52) ?_
  refine Eq.trans (step_accOf _ v53) ?_
  refine Eq.trans (step_accOf _ (vM 0)) ?_
  refine Eq.trans (step_accOf _ (vM 1)) ?_
  refine Eq.trans (step_accOf _ (vM 2)) ?_
  refine Eq.trans (step_accOf _ (vM 3)) ?_
  refine Eq.trans (step_accOf _ (vM 4)) ?_
  refine Eq.trans (step_accOf _ (vM 5)) ?_
  refine Eq.trans (step_accOf _ (vM 6)) ?_
  refine Eq.trans (step_accOf _ (vM 7)) ?_
  refine Eq.trans (step_accOf _ (vM 8)) ?_
  refine Eq.trans (step_accOf _ (vM 9)) ?_
  refine Eq.trans (step_accOf _ (vM 10)) ?_
  rfl







/-- One block: the registers of block `i + 1` are the step of the registers of block
`i`, in the encoding of `HoldsRegs`. -/
theorem holdsRegs_stepBlock (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) {i : ℕ} (hi : i < bufferLen)
    (h : HoldsRegs (evalSteps env (stepsUpTo input i)) i (runOf input env i)) :
    HoldsRegs (evalSteps env (stepsUpTo input (i + 1))) (i + 1) (runOf input env (i + 1)) := by
  have hb : Witness.bytesOf input env i < 256 := by
    simp only [Witness.bytesOf, dif_pos hi]; exact hbytes i hi
  have hLsize : (evalSteps env (stepsUpTo input i)).size = nRegs + blockSize * i := by
    rw [size_evalSteps, length_stepsUpTo]; simp
  have hrun : runOf input env (i + 1)
      = nextRegs (runOf input env i) (Witness.bytesOf input env i)
          (decide (i < Witness.lenOf input env)) := by
    simp only [runOf, run_succ, nextRegs, Witness.bytesOf, dif_pos hi]
    split <;> rename_i hc <;> simp [hc]
  rw [stepsUpTo_succ, evalSteps_append,
    evalSteps_stepBlock input env hi hb rfl rfl hlen hLsize h
      (run_hexAcc_lt _ _ i) (run_kIdx_le _ _ i) (run_ofs_le _ _ i)
      (le_trans (run_nMem_le _ _ i) (le_of_lt hi)), hrun]
  have hget : ∀ off, off < nRegs →
      (evalSteps env (stepsUpTo input i) ++
          accOf (blockVal (runOf input env i) (Witness.bytesOf input env i)
            (decide (i < Witness.lenOf input env))) blockSize)[regBase (i + 1) + off]?
        = some (.inr (UInt64.ofNat (blockVal (runOf input env i) (Witness.bytesOf input env i)
            (decide (i < Witness.lenOf input env)) (nSigs + off)))) := by
    intro off hoff
    have he : regBase (i + 1) + off
        = (evalSteps env (stepsUpTo input i)).size + (nSigs + off) := by
      rw [hLsize, regBase, Nat.mul_succ]
      have hbs : blockSize = nRegs + nSigs := rfl
      omega
    rw [he, getElem?_append_add,
      getElem?_accOf _ (by simp only [blockSize]; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hget rST (by decide)
  · exact hget rSUB (by decide)
  · exact hget rHEXACC (by decide)
  · exact hget rKIDX (by decide)
  · exact hget rCLAIM (by decide)
  · exact hget rOFS (by decide)
  · exact hget rNMEM (by decide)
  · intro k
    rw [hget (rM + k.val) (by have := k.isLt; simp only [nRegs, rM, Model.nClaims] at *; omega)]
    have hidx : nSigs + (rM + k.val) = k.val + 54 := by simp only [nSigs, rM]; omega
    rw [hidx]
    have hbv : blockVal (runOf input env i) (Witness.bytesOf input env i)
        (decide (i < Witness.lenOf input env)) (k.val + 54)
        = ub ((nextRegs (runOf input env i) (Witness.bytesOf input env i)
            (decide (i < Witness.lenOf input env))).m[k.val]'k.isLt) := by
      simp only [blockVal, dif_pos k.isLt]
    rw [hbv]
    cases hm : (nextRegs (runOf input env i) (Witness.bytesOf input env i)
        (decide (i < Witness.lenOf input env))).m[k.val]'k.isLt <;> simp [ub, hm]

/-- The locals of the prefix up to position `i` hold the run at `i`. -/
theorem holdsRegs_stepsUpTo (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) {i : ℕ} (hi : i ≤ bufferLen) :
    HoldsRegs (evalSteps env (stepsUpTo input i)) i (runOf input env i) := by
  induction i with
  | zero =>
      have hL : evalSteps env (stepsUpTo input 0) = evalSteps env initBlock #[] := by
        simp only [stepsUpTo, List.range_zero, List.flatMap_nil, List.append_nil]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [hL, initBlock, nClaims, List.replicate, List.cons_append, List.nil_append,
          evalSteps, Witgen.U64Expr.eval, cst, regBase, rST, rSUB, rHEXACC, rKIDX, rCLAIM,
          rOFS, rNMEM, rM, claimCode, Nat.mul_zero, Nat.zero_add, Nat.add_zero] <;>
        first
          | (intro k; fin_cases k <;> simp [runOf, Model.run, Model.Regs.init])
          | simp [runOf, Model.run, Model.Regs.init, claimNone]
  | succ i ih => exact holdsRegs_stepBlock input env hbytes hlen (by omega) (ih (by omega))

/-- Every local of the block of position `i`, read out of the whole program. -/
theorem blockVal_runSteps (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) {i : ℕ} (hi : i < bufferLen) {m : ℕ}
    (hm : m < blockSize) :
    (evalSteps env (runSteps input))[sigBase i + m]?
      = some (.inr (UInt64.ofNat (blockVal (runOf input env i) (Witness.bytesOf input env i)
          (decide (i < Witness.lenOf input env)) m))) := by
  have hb : Witness.bytesOf input env i < 256 := by
    simp only [Witness.bytesOf, dif_pos hi]; exact hbytes i hi
  have hLsize : (evalSteps env (stepsUpTo input i)).size = nRegs + blockSize * i := by
    rw [size_evalSteps, length_stepsUpTo]; simp
  have hpref : (evalSteps env (runSteps input))[sigBase i + m]?
      = (evalSteps env (stepsUpTo input (i + 1)))[sigBase i + m]? := by
    refine getElem?_runSteps_of_lt input env (by omega) ?_
    simp only [sigBase]
    rw [Nat.mul_succ]
    omega
  rw [hpref, stepsUpTo_succ, evalSteps_append,
    evalSteps_stepBlock input env hi hb rfl rfl hlen hLsize
      (holdsRegs_stepsUpTo input env hbytes hlen (le_of_lt hi))
      (run_hexAcc_lt _ _ i) (run_kIdx_le _ _ i) (run_ofs_le _ _ i)
      (le_trans (run_nMem_le _ _ i) (le_of_lt hi))]
  have he : sigBase i + m = (evalSteps env (stepsUpTo input i)).size + m := by
    rw [hLsize]; simp only [sigBase]; omega
  rw [he, getElem?_append_add, getElem?_accOf _ hm]

/-- The locals of the whole program hold the run at every block. -/
theorem holdsRegs_runSteps (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) {i : ℕ} (hi : i ≤ bufferLen) :
    HoldsRegs (evalSteps env (runSteps input)) i (runOf input env i) := by
  have hpref : ∀ off, off < nRegs →
      (evalSteps env (runSteps input))[regBase i + off]?
        = (evalSteps env (stepsUpTo input i))[regBase i + off]? := by
    intro off hoff
    refine getElem?_runSteps_of_lt input env hi ?_
    simp only [regBase]; omega
  have h := holdsRegs_stepsUpTo input env hbytes hlen hi
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpref rST (by decide)]; exact h1
  · rw [hpref rSUB (by decide)]; exact h2
  · rw [hpref rHEXACC (by decide)]; exact h3
  · rw [hpref rKIDX (by decide)]; exact h4
  · rw [hpref rCLAIM (by decide)]; exact h5
  · rw [hpref rOFS (by decide)]; exact h6
  · rw [hpref rNMEM (by decide)]; exact h7
  · intro k
    rw [hpref (rM + k.val) (by have := k.isLt; simp only [nRegs, rM]; omega)]
    exact h8 k

/-! The program is sealed here: from this point on `runSteps` is an opaque list, so that
neither the bridges below nor `elaborate_circuit` ever try to evaluate a 66578-step
program at `whnf`. Everything about it is used through `holdsRegs_runSteps` from here on. -/

attribute [irreducible] initBlock stepBlock stepsUpTo runSteps

/-- Every block index a read-out uses is in range. -/
theorem div_le_bufferLen {idx n : ℕ} (_hn : 0 < n) (hidx : idx < n * slots) :
    idx / n ≤ bufferLen := by
  have : idx / n < slots := Nat.div_lt_of_lt_mul (by omega)
  simp only [Witness.slots] at this
  omega

/-! ### The signals of the honest run

`Model.runSignals` plugs the *actual* successor state into `Model.signals`, `sigOf` the
one the program computes; they differ only in `keyStart`, which no read-out looks at. -/

theorem runSignals_match_pos {bytes : ℕ → ℕ} {len i : ℕ} (h : i < len) (k : Model.Claim) :
    (Model.runSignals bytes len i).match_[k]
      = (sigOf (Model.run bytes len i) (bytes i)).match_[k] := by
  simp only [Model.runSignals, if_pos h]; rfl

theorem runSignals_vEmit_pos {bytes : ℕ → ℕ} {len i : ℕ} (h : i < len) :
    (Model.runSignals bytes len i).vEmit = (sigOf (Model.run bytes len i) (bytes i)).vEmit := by
  simp only [Model.runSignals, if_pos h]; rfl

theorem runSignals_minusFlag_pos {bytes : ℕ → ℕ} {len i : ℕ} (h : i < len) :
    (Model.runSignals bytes len i).minusFlag
      = (sigOf (Model.run bytes len i) (bytes i)).minusFlag := by
  simp only [Model.runSignals, if_pos h]; rfl

theorem runSignals_trueDone_pos {bytes : ℕ → ℕ} {len i : ℕ} (h : i < len) :
    (Model.runSignals bytes len i).trueDone
      = (sigOf (Model.run bytes len i) (bytes i)).trueDone := by
  simp only [Model.runSignals, if_pos h]; rfl

theorem runSignals_write_pos {bytes : ℕ → ℕ} {len i : ℕ} (h : i < len) :
    (Model.runSignals bytes len i).write = (sigOf (Model.run bytes len i) (bytes i)).write := by
  simp only [Model.runSignals, if_pos h]; rfl

theorem runSignals_valOut_pos {bytes : ℕ → ℕ} {len i : ℕ} (h : i < len) :
    (Model.runSignals bytes len i).valOut
      = (sigOf (Model.run bytes len i) (bytes i)).valOut := by
  simp only [Model.runSignals, if_pos h]; rfl

theorem runSignals_match_neg {bytes : ℕ → ℕ} {len i : ℕ} (h : ¬ i < len) (k : Model.Claim) :
    (Model.runSignals bytes len i).match_[k] = false := by
  simp [Model.runSignals, if_neg h]

theorem runSignals_vEmit_neg {bytes : ℕ → ℕ} {len i : ℕ} (h : ¬ i < len) :
    (Model.runSignals bytes len i).vEmit = false := by simp [Model.runSignals, if_neg h]

theorem runSignals_minusFlag_neg {bytes : ℕ → ℕ} {len i : ℕ} (h : ¬ i < len) :
    (Model.runSignals bytes len i).minusFlag = false := by simp [Model.runSignals, if_neg h]

theorem runSignals_trueDone_neg {bytes : ℕ → ℕ} {len i : ℕ} (h : ¬ i < len) :
    (Model.runSignals bytes len i).trueDone = false := by simp [Model.runSignals, if_neg h]

theorem runSignals_write_neg {bytes : ℕ → ℕ} {len i : ℕ} (h : ¬ i < len) :
    (Model.runSignals bytes len i).write = false := by simp [Model.runSignals, if_neg h]

/-! ### At most one claim matches a closing key

`Model.presentCount` counts the positions where claim `k`'s matcher fires, while the
program stores the *first* matching claim; the two agree because two live matchers agree
on every code point of the key consumed so far, and the claim names are distinct. -/

/-- Two live matchers agree on the key consumed so far. -/
def MatchInv (r : Model.Regs) : Prop :=
  ∀ k k' : Model.Claim, r.m[k] = true → r.m[k'] = true →
    ∀ j, j < r.kIdx → Model.nameAt k j = Model.nameAt k' j

theorem matchInv_init : MatchInv Model.Regs.init := by
  intro k k' hk _ _ _
  simp [Model.Regs.init] at hk

theorem step_matchInv {r r' : Model.Regs} {b : ℕ} (hinv : MatchInv r)
    (hk15 : r.kIdx ≤ kIdxMax - 1) (h : Model.step r b = some r') : MatchInv r' := by
  obtain ⟨-, -, -, hkidx, -, -, -, hm⟩ := step_some_fields h
  simp only [Model.kIdxMax] at hk15 hkidx
  intro k k' hk hk' j hj
  rw [hm k] at hk
  rw [hm k'] at hk'
  by_cases hks : (sigOf r b).keyStart = true
  · exfalso
    have hst : r.st ≠ Model.St.KEY := by
      have h2 := hks
      rw [sigOf_keyStart] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq] at h2
      exact h2.2
    rw [hkidx, if_neg hst] at hj
    omega
  · simp only [Bool.not_eq_true] at hks
    rw [hks] at hk hk'
    simp only [Bool.false_eq_true, if_false] at hk hk'
    by_cases hst : r.st = Model.St.KEY
    · rw [if_pos hst] at hk hk'
      rw [hkidx, if_pos hst] at hj
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk hk'
      obtain ⟨hmk, hek⟩ := hk
      obtain ⟨hmk', hek'⟩ := hk'
      by_cases hemit : (sigOf r b).emit = true
      · simp only [hemit, ub, if_true] at hj
        rcases Nat.lt_or_ge j r.kIdx with hjk | hjk
        · exact hinv k k' hmk hmk' j hjk
        · have hjeq : j = r.kIdx := by omega
          subst hjeq
          rcases hek with hek | hek
          · rw [hek] at hemit; simp at hemit
          · rcases hek' with hek' | hek'
            · rw [hek'] at hemit; simp at hemit
            · simp only [decide_eq_true_eq] at hek hek'
              rw [← hek, ← hek']
      · simp only [Bool.not_eq_true] at hemit
        simp only [hemit, ub, Bool.false_eq_true, if_false, Nat.add_zero] at hj
        exact hinv k k' hmk hmk' j (by omega)
    · rw [if_neg hst] at hk
      simp at hk

theorem run_matchInv (bytes : ℕ → ℕ) (len i : ℕ) : MatchInv (Model.run bytes len i) := by
  induction i with
  | zero => exact matchInv_init
  | succ i ih =>
      rw [run_succ]
      split
      · cases hs : Model.step (Model.run bytes len i) (bytes i) with
        | none => simpa using ih
        | some r' => simpa using step_matchInv ih (run_kIdx_le bytes len i) hs
      · exact ih

theorem claimName_inj : ∀ k k' : Model.Claim, Model.claimName k = Model.claimName k' → k = k' := by
  decide

theorem match_unique {r : Model.Regs} (hinv : MatchInv r) {b : ℕ} {k k' : Model.Claim}
    (hk : (sigOf r b).match_[k] = true) (hk' : (sigOf r b).match_[k'] = true) : k = k' := by
  rw [sigOf_match] at hk
  rw [sigOf_match] at hk'
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

/-- The program's matched-claim index decides the model's matcher. -/
theorem decide_matchIdxOf {r : Model.Regs} (hinv : MatchInv r) (b : ℕ) (k : Model.Claim) :
    decide (matchIdxOf r b = k.val) = (sigOf r b).match_[k] := by
  have hk11 : k.val < nClaims := k.isLt
  simp only [Model.nClaims] at hk11
  cases hf : (List.finRange nClaims).find? (fun j => (sigOf r b).match_[j]) with
  | none =>
      have hpk : (sigOf r b).match_[k] = false := by
        have := List.find?_eq_none.mp hf k (List.mem_finRange k)
        simpa using this
      rw [hpk]
      simp only [matchIdxOf, hf, claimCode, Option.elim, decide_eq_false_iff_not, claimNone,
        Model.nClaims]
      omega
  | some j =>
      have hpj : (sigOf r b).match_[j] = true := by
        simpa using List.find?_eq_some_iff_getElem.mp hf |>.1
      simp only [matchIdxOf, hf, claimCode, Option.elim]
      by_cases hc : (sigOf r b).match_[k] = true
      · rw [hc, match_unique hinv hpj hc]
        simp
      · simp only [Bool.not_eq_true] at hc
        rw [hc, decide_eq_false_iff_not]
        intro heq
        have hjk : j = k := Fin.ext heq
        rw [hjk, hc] at hpj
        simp at hpj

/-! ### The eleven bridges

Each witness site's IR program produces exactly the vector `Witness.lean` projects out
of the run, under the two hypotheses of `ProverAssumptions` the truncation needs. -/

/-! ### Elementwise read-out lemmas

Stated over an *arbitrary* locals array: the kernel does not honour `irreducible`, so a
proof whose defeq obligations mention `runSteps` would unfold a 66578-step list. Keeping
`L` a variable here means the layout theorem is the only place the program is ever
unfolded. -/

/-- One entry of the one-hot main-state read-out. -/
theorem getElem_eval_stOut (env : ProverEnvironment Fp) (L : Array (Fp ⊕ UInt64))
    (idx : ℕ) (hidx : idx < nSt * slots) {r : Model.Regs} (h : HoldsRegs L (idx / nSt) r) :
    (Witgen.VExpr.eval { env := env, locals := L } stOut)[idx]'hidx
      = Witness.ind (decide (r.st.val = idx % nSt)) := by
  have hst : r.st.val < 2 ^ 64 := Nat.lt_trans (Fin.isLt _) nSt_lt64
  have hmod : idx % nSt < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by decide)) nSt_lt64
  simp only [stOut, Witgen.VExpr.eval, Vector.getElem_map, Vector.getElem_ofFn, toF, reg, cst,
    Witgen.FExpr.eval, Witgen.BExpr.eval, Witgen.U64Expr.eval, h.1, Witness.ind,
    decide_eq_true_eq, ofNat_inj hst hmod]

/-- One entry of the one-hot sub-state read-out. -/
theorem getElem_eval_subOut (env : ProverEnvironment Fp) (L : Array (Fp ⊕ UInt64))
    (idx : ℕ) (hidx : idx < nSub * slots) {r : Model.Regs} (h : HoldsRegs L (idx / nSub) r) :
    (Witgen.VExpr.eval { env := env, locals := L } subOut)[idx]'hidx
      = Witness.ind (decide (r.sub.val = idx % nSub)) := by
  have hst : r.sub.val < 2 ^ 64 := Nat.lt_trans (Fin.isLt _) nSub_lt64
  have hmod : idx % nSub < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by decide)) nSub_lt64
  simp only [subOut, Witgen.VExpr.eval, Vector.getElem_map, Vector.getElem_ofFn, toF, reg, cst,
    Witgen.FExpr.eval, Witgen.BExpr.eval, Witgen.U64Expr.eval, h.2.1, Witness.ind,
    decide_eq_true_eq, ofNat_inj hst hmod]

/-- One entry of the key-matcher read-out. -/
theorem getElem_eval_mOut (env : ProverEnvironment Fp) (L : Array (Fp ⊕ UInt64))
    (idx : ℕ) (hidx : idx < nClaims * slots) {r : Model.Regs}
    (h : HoldsRegs L (idx / nClaims) r) :
    (Witgen.VExpr.eval { env := env, locals := L } mOut)[idx]'hidx
      = Witness.ind (r.m[idx % nClaims]'(Nat.mod_lt _ (by decide))) := by
  have hk := h.2.2.2.2.2.2.2 ⟨idx % nClaims, Nat.mod_lt _ (by decide)⟩
  simp only [mOut, Witgen.VExpr.eval, Vector.getElem_map, Vector.getElem_ofFn, toF, reg, cst,
    Witgen.FExpr.eval, Witgen.BExpr.eval, Witgen.U64Expr.eval, hk, Witness.ind]
  split <;> simp_all

/-- One entry of the claim-register read-out. -/
theorem getElem_eval_claimOut (env : ProverEnvironment Fp) (L : Array (Fp ⊕ UInt64))
    (idx : ℕ) (hidx : idx < nClaims * slots) {r : Model.Regs}
    (h : HoldsRegs L (idx / nClaims) r) :
    (Witgen.VExpr.eval { env := env, locals := L } claimOut)[idx]'hidx
      = Witness.ind (decide (r.claim = some ⟨idx % nClaims, Nat.mod_lt _ (by decide)⟩)) := by
  have hmod : idx % nClaims < nClaims := Nat.mod_lt _ (by decide)
  have hmod64 : idx % nClaims < 2 ^ 64 := Nat.lt_trans hmod (Nat.lt_of_succ_lt nClaims_succ_lt64)
  have hcc : claimCode r.claim < 2 ^ 64 := by
    unfold claimCode
    cases r.claim with
    | none => exact Nat.lt_trans (by decide : claimNone < nClaims + 1) nClaims_succ_lt64
    | some k => exact Nat.lt_trans (Fin.isLt _) (Nat.lt_of_succ_lt nClaims_succ_lt64)
  simp only [claimOut, Witgen.VExpr.eval, Vector.getElem_map, Vector.getElem_ofFn, toF, reg, cst,
    Witgen.FExpr.eval, Witgen.BExpr.eval, Witgen.U64Expr.eval, h.2.2.2.2.1, Witness.ind,
    decide_eq_true_eq, ofNat_inj hcc hmod64, claimCode_eq_iff hmod]

/-- One entry of a nat-valued register read-out. -/
theorem getElem_eval_natOut (env : ProverEnvironment Fp) (L : Array (Fp ⊕ UInt64))
    (off i v : ℕ) (hi : i < slots) (hv : v < 2 ^ 64)
    (h : L[regBase i + off]? = some (.inr (UInt64.ofNat v))) :
    (Witgen.VExpr.eval { env := env, locals := L } (natOut off))[i]'hi = (v : Fp) := by
  simp only [natOut, Witgen.VExpr.eval, Vector.getElem_map, Vector.getElem_ofFn, reg,
    Witgen.FExpr.eval, Witgen.U64Expr.eval, h]
  exact fromNat_ofNat hv

/-! ### The eleven bridges

Each witness site's IR program produces exactly the vector `Witness.lean` projects out of
the run, under the two hypotheses of `ProverAssumptions` the truncation needs. -/

theorem eval_stIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (stIR input).eval env
      = Witness.stGen (Witness.bytesOf input env) (Witness.lenOf input env) := by
  ext idx hidx
  simp only [stIR, WitgenIR.eval, Witness.stGen, Vector.getElem_ofFn]
  exact getElem_eval_stOut env _ idx hidx
    (holdsRegs_runSteps input env hbytes hlen (div_le_bufferLen (by decide) hidx))

theorem eval_subIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (subIR input).eval env
      = Witness.subGen (Witness.bytesOf input env) (Witness.lenOf input env) := by
  ext idx hidx
  simp only [subIR, WitgenIR.eval, Witness.subGen, Vector.getElem_ofFn]
  exact getElem_eval_subOut env _ idx hidx
    (holdsRegs_runSteps input env hbytes hlen (div_le_bufferLen (by decide) hidx))

theorem eval_mIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (mIR input).eval env
      = Witness.mGen (Witness.bytesOf input env) (Witness.lenOf input env) := by
  ext idx hidx
  simp only [mIR, WitgenIR.eval, Witness.mGen, Vector.getElem_ofFn]
  exact getElem_eval_mOut env _ idx hidx
    (holdsRegs_runSteps input env hbytes hlen (div_le_bufferLen (by decide) hidx))

theorem eval_claimIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (claimIR input).eval env
      = Witness.claimGen (Witness.bytesOf input env) (Witness.lenOf input env) := by
  ext idx hidx
  simp only [claimIR, WitgenIR.eval, Witness.claimGen, Vector.getElem_ofFn]
  exact getElem_eval_claimOut env _ idx hidx
    (holdsRegs_runSteps input env hbytes hlen (div_le_bufferLen (by decide) hidx))

/-- The four nat-valued registers share one bridge. -/
private theorem eval_natIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (off : ℕ) (val : Model.Regs → ℕ)
    (hget : ∀ (L : Array (Fp ⊕ UInt64)) (i : ℕ) (r : Model.Regs), HoldsRegs L i r →
      L[regBase i + off]? = some (.inr (UInt64.ofNat (val r))))
    (hbd : ∀ i ≤ bufferLen, val (runOf input env i) < 2 ^ 64)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (WitgenIR.ir (runSteps input) (natOut off)).eval env
      = Vector.ofFn fun i : Fin slots => ((val (runOf input env i.val) : ℕ) : Fp) := by
  ext i hi
  have hb : i ≤ bufferLen := by simp only [Witness.slots] at hi; omega
  simp only [WitgenIR.eval, Vector.getElem_ofFn]
  exact getElem_eval_natOut env _ off i _ hi (hbd i hb)
    (hget _ _ _ (holdsRegs_runSteps input env hbytes hlen hb))

theorem eval_hexAccIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (hexAccIR input).eval env
      = Witness.hexAccGen (Witness.bytesOf input env) (Witness.lenOf input env) :=
  eval_natIR input env rHEXACC Model.Regs.hexAcc (fun _ _ _ h => h.2.2.1)
    (fun i _ => lt_trans (run_hexAcc_lt _ _ i) (by norm_num)) hbytes hlen

theorem eval_kIdxIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (kIdxIR input).eval env
      = Witness.kIdxGen (Witness.bytesOf input env) (Witness.lenOf input env) :=
  eval_natIR input env rKIDX Model.Regs.kIdx (fun _ _ _ h => h.2.2.2.1)
    (fun i _ => lt_of_le_of_lt (run_kIdx_le _ _ i) (by norm_num [Model.kIdxMax])) hbytes hlen

theorem eval_ofsIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (ofsIR input).eval env
      = Witness.ofsGen (Witness.bytesOf input env) (Witness.lenOf input env) :=
  eval_natIR input env rOFS Model.Regs.ofs (fun _ _ _ h => h.2.2.2.2.2.1)
    (fun i _ => lt_of_le_of_lt (run_ofs_le _ _ i) (by norm_num [Model.ofsMax])) hbytes hlen

theorem eval_nMemIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (nMemIR input).eval env
      = Witness.nMemGen (Witness.bytesOf input env) (Witness.lenOf input env) :=
  eval_natIR input env rNMEM Model.Regs.nMem (fun _ _ _ h => h.2.2.2.2.2.2.1)
    (fun i hi => lt64_of_le_bufferLen (le_trans (run_nMem_le _ _ i) hi)) hbytes hlen

theorem eval_lenFlagsIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hlen : (env input.len).val ≤ bufferLen) :
    (lenFlagsIR input).eval env = Witness.lenFlagsGen (Witness.lenOf input env) := by
  have hlenOf : FiniteField.val (Expression.eval env.toEnvironment input.len)
      = Witness.lenOf input env := rfl
  have hl64 : Witness.lenOf input env < 2 ^ 64 :=
    lt64_of_le_bufferLen (by simpa only [Witness.lenOf] using hlen)
  ext i hi
  have hi64 : i < 2 ^ 64 := lt64_of_le_bufferLen (by simp only [Witness.slots] at hi; omega)
  have hkey : (UInt64.ofNat i = UInt64.ofNat (Witness.lenOf input env))
      = (i = Witness.lenOf input env) := propext (ofNat_inj hi64 hl64)
  simp only [lenFlagsIR, WitgenIR.eval, lenFlagsOut, Witgen.VExpr.eval, Vector.getElem_mapRange,
    toF, lenE, Witgen.FExpr.eval, Witgen.BExpr.eval, Witgen.U64Expr.eval, hlenOf, hkey,
    Witness.lenFlagsGen, Vector.getElem_ofFn, Witness.ind, decide_eq_true_eq]

theorem eval_accmIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hlen : (env input.len).val ≤ bufferLen) :
    (accmIR input).eval env = Witness.accmGen (Witness.lenOf input env) := by
  have hlenOf : FiniteField.val (Expression.eval env.toEnvironment input.len)
      = Witness.lenOf input env := rfl
  have hl64 : Witness.lenOf input env < 2 ^ 64 :=
    lt64_of_le_bufferLen (by simpa only [Witness.lenOf] using hlen)
  ext i hi
  simp only [Witness.slots] at hi
  have hi64 : i < 2 ^ 64 := lt64_of_le_bufferLen (by omega)
  have hkey : (UInt64.ofNat (Witness.lenOf input env) < UInt64.ofNat i)
      = (Witness.lenOf input env < i) := propext (ofNat_lt_ofNat hl64 hi64)
  simp only [accmIR, WitgenIR.eval, accmOut, Witgen.VExpr.eval, Vector.getElem_mapRange,
    toF, lenE, Witgen.FExpr.eval, Witgen.BExpr.eval, Witgen.U64Expr.eval, hlenOf, hkey,
    Witness.accmGen, Vector.getElem_ofFn, Witness.ind, decide_eq_true_eq]

/-! ### Counting and first-match folds

`countE` is a sum of `0`/`1` indicators over all `bufferLen` positions and `cellE` a
right fold that keeps the first hit; the model counts and searches only the `len` active
positions, and the program's signals are off past `len`. -/

/-- Stated over an abstract context: a `rfl` on a context that mentions `runSteps` makes
the kernel (which ignores `irreducible`) unfold the whole 66578-step program. -/
theorem eval_ofU64 (ctx : Witgen.Ctx Fp) (x : UE) :
    Witgen.FExpr.eval ctx (.ofU64 x) = FiniteField.fromNat (Witgen.U64Expr.eval ctx x).toNat := rfl

theorem eval_toF (ctx : Witgen.Ctx Fp) (c : BE) :
    Witgen.FExpr.eval ctx (toF c) = if Witgen.BExpr.eval ctx c then (1 : Fp) else 0 := rfl

theorem eval_count_foldr {ctx : Witgen.Ctx Fp} {P : ℕ → BE} {q : ℕ → Bool} :
    ∀ l : List ℕ, (∀ i ∈ l, Witgen.BExpr.eval ctx (P i) = q i) →
      Witgen.FExpr.eval ctx (l.foldr (fun i acc => .add (toF (P i)) acc) (.const 0))
        = (((l.filter q).length : ℕ) : Fp)
  | [], _ => by
      simp only [List.foldr_nil, Witgen.FExpr.eval, List.filter_nil, List.length_nil,
        Nat.cast_zero]
  | a :: l, hP => by
      have ih := eval_count_foldr l (fun i hi => hP i (by simp [hi]))
      rw [List.foldr_cons, show Witgen.FExpr.eval ctx
          (Witgen.FExpr.add (toF (P a))
            (l.foldr (fun i acc => Witgen.FExpr.add (toF (P i)) acc) (.const 0)))
          = Witgen.FExpr.eval ctx (toF (P a))
            + Witgen.FExpr.eval ctx
              (l.foldr (fun i acc => Witgen.FExpr.add (toF (P i)) acc) (.const 0)) from rfl,
        ih, eval_toF, hP a (by simp), List.filter_cons]
      cases hq : q a <;> simp [hq] <;> ring

theorem eval_first_foldr {ctx : Witgen.Ctx Fp} {P : ℕ → BE} {X : ℕ → UE} {q : ℕ → Bool}
    {valOf : ℕ → ℕ} :
    ∀ l : List ℕ, (∀ i ∈ l, Witgen.BExpr.eval ctx (P i) = q i) →
      (∀ i ∈ l, q i = true → Witgen.FExpr.eval ctx (.ofU64 (X i)) = ((valOf i : ℕ) : Fp)) →
      Witgen.FExpr.eval ctx (l.foldr (fun i acc => .ite (P i) (.ofU64 (X i)) acc) (.const 0))
        = (((l.find? q).elim 0 valOf : ℕ) : Fp)
  | [], _, _ => by
      simp only [List.foldr_nil, Witgen.FExpr.eval, List.find?_nil, Option.elim, Nat.cast_zero]
  | a :: l, hP, hX => by
      have ih := eval_first_foldr l (fun i hi => hP i (by simp [hi]))
        (fun i hi => hX i (by simp [hi]))
      simp only [List.foldr_cons, Witgen.FExpr.eval, List.find?_cons, hP a (by simp)]
      cases hq : q a with
      | true =>
          simp only [if_true, Option.elim]
          exact hX a (by simp) hq
      | false => simpa using ih

/-- Positions past `len` never contribute to a count. -/
theorem filter_range_trunc (q : ℕ → Bool) {len n : ℕ} (hle : len ≤ n)
    (h : ∀ i, len ≤ i → q i = false) :
    ((List.range n).filter q).length = ((List.range len).filter q).length := by
  induction n, hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      simp [h n hn]

/-- Positions past `len` never win a first-match fold. -/
theorem find?_range_trunc (q : ℕ → Bool) {len n : ℕ} (hle : len ≤ n)
    (h : ∀ i, len ≤ i → q i = false) :
    (List.range n).find? q = (List.range len).find? q := by
  induction n, hle using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [List.range_succ, List.find?_append, ih]
      cases hf : (List.range len).find? q with
      | some x => rfl
      | none => simp [h n hn]

/-! ### The four counts and the cell read-out -/

theorem blockVal_valOut (r : Model.Regs) (b : ℕ) (active : Bool) :
    blockVal r b active sVALOUT = (sigOf r b).valOut := rfl

theorem blockVal_cellIdx (r : Model.Regs) (b : ℕ) (active : Bool) :
    blockVal r b active sCELLIDX
      = if active && (sigOf r b).write then claimCode r.claim * ofsMax + r.ofs else cellNone := rfl

theorem blockVal_matchOut (r : Model.Regs) (b : ℕ) (active : Bool) :
    blockVal r b active sMATCHOUT = if active then matchIdxOf r b else claimNone := rfl

theorem blockVal_vEmitC (r : Model.Regs) (b : ℕ) (active : Bool) :
    blockVal r b active sVEMITC
      = if active && (sigOf r b).vEmit then claimCode r.claim else claimNone := rfl

theorem blockVal_minusC (r : Model.Regs) (b : ℕ) (active : Bool) :
    blockVal r b active sMINUSC
      = if active && (sigOf r b).minusFlag then claimCode r.claim else claimNone := rfl

theorem blockVal_trueC (r : Model.Regs) (b : ℕ) (active : Bool) :
    blockVal r b active sTRUEC
      = if active && (sigOf r b).trueDone then claimCode r.claim else claimNone := rfl


/-- A signal local of the whole program, as a bounded natural number. -/
theorem uis_sig (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) {i : ℕ} (hi : i < bufferLen) {off : ℕ}
    (hoff : off < blockSize)
    (hbd : blockVal (runOf input env i) (Witness.bytesOf input env i)
        (decide (i < Witness.lenOf input env)) off < 2 ^ 64) :
    UIs { env := env, locals := evalSteps env (runSteps input) } (sigl i off)
      (blockVal (runOf input env i) (Witness.bytesOf input env i)
        (decide (i < Witness.lenOf input env)) off) :=
  UIs.localVar hbd (blockVal_runSteps input env hbytes hlen hi hoff)

theorem eval_presentE (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) :
    Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) } (presentE k.val)
      = ((Model.presentCount (Witness.bytesOf input env) (Witness.lenOf input env) k : ℕ)
          : Fp) := by
  have hk : k.val < nClaims := k.isLt
  simp only [Model.nClaims] at hk
  have hP : ∀ i ∈ List.range bufferLen,
      Witgen.BExpr.eval { env := env, locals := evalSteps env (runSteps input) }
          (.neq (sigl i sMATCHOUT) (cst k.val))
        = (Model.runSignals (Witness.bytesOf input env) (Witness.lenOf input env) i).match_[k] := by
    intro i hi
    have hib : i < bufferLen := List.mem_range.mp hi
    have hbd : blockVal (runOf input env i) (Witness.bytesOf input env i)
        (decide (i < Witness.lenOf input env)) sMATCHOUT < 2 ^ 64 := by
      rw [blockVal_matchOut]
      split
      · exact matchIdxOf_lt _ _
      · simp only [claimNone, Model.nClaims]; norm_num
    rw [eval_neqU (uis_sig input env hbytes hlen hib (by decide) hbd) (UIs.cst (by omega))]
    rw [blockVal_matchOut]
    split <;> rename_i hact
    · have hact' : i < Witness.lenOf input env := by simpa using hact
      rw [runSignals_match_pos hact' k, decide_matchIdxOf (run_matchInv _ _ i)]
    · have hact' : ¬ i < Witness.lenOf input env := by simpa using hact
      rw [runSignals_match_neg hact' k]
      simp only [claimNone, Model.nClaims]
      exact decide_eq_false (by omega)
  rw [presentE, countE, eval_count_foldr _ hP,
    filter_range_trunc _ (len := Witness.lenOf input env) (n := bufferLen) hlen
      (fun i hi => runSignals_match_neg (Nat.not_lt.mpr hi) k)]
  simp only [Model.presentCount]

/-- The tail of a count proof: once the per-position predicate is identified, the sum is
the model's filter length over the active prefix. -/
theorem eval_countE_of (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hlen : (env input.len).val ≤ bufferLen) (off k : ℕ) (q : ℕ → Bool)
    (hP : ∀ i ∈ List.range bufferLen,
      Witgen.BExpr.eval { env := env, locals := evalSteps env (runSteps input) }
        (.neq (sigl i off) (cst k)) = q i)
    (hpast : ∀ i, Witness.lenOf input env ≤ i → q i = false) :
    Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) } (countE off k)
      = ((((List.range (Witness.lenOf input env)).filter q).length : ℕ) : Fp) := by
  rw [countE, eval_count_foldr _ hP]
  exact congrArg (fun n : ℕ => (n : Fp))
    (filter_range_trunc _ (len := Witness.lenOf input env) (n := bufferLen) hlen hpast)

/-- The three claim-tagged counts: a per-position flag gated by the active flag, carrying
the claim register when it fires. -/
theorem eval_claimCount (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (off : ℕ) (hoff : off < blockSize)
    (fld : Model.Signals → Bool) (k : Model.Claim)
    (hb : ∀ i, blockVal (runOf input env i) (Witness.bytesOf input env i)
        (decide (i < Witness.lenOf input env)) off
      = if decide (i < Witness.lenOf input env)
          && fld (sigOf (runOf input env i) (Witness.bytesOf input env i))
        then claimCode (runOf input env i).claim else claimNone)
    (hpos : ∀ i, i < Witness.lenOf input env →
      fld (Model.runSignals (Witness.bytesOf input env) (Witness.lenOf input env) i)
        = fld (sigOf (runOf input env i) (Witness.bytesOf input env i)))
    (hneg : ∀ i, ¬ i < Witness.lenOf input env →
      fld (Model.runSignals (Witness.bytesOf input env) (Witness.lenOf input env) i) = false) :
    ∀ i ∈ List.range bufferLen,
      Witgen.BExpr.eval { env := env, locals := evalSteps env (runSteps input) }
          (.neq (sigl i off) (cst k.val))
        = (fld (Model.runSignals (Witness.bytesOf input env) (Witness.lenOf input env) i) &&
            decide ((runOf input env i).claim = some k)) := by
  have hk : k.val < nClaims := k.isLt
  have hk' : k.val < nClaims := k.isLt
  simp only [Model.nClaims] at hk
  intro i hi
  have hib : i < bufferLen := List.mem_range.mp hi
  have hcc : claimCode (runOf input env i).claim < 2 ^ 64 := by
    cases hc : (runOf input env i).claim with
    | none => simp only [claimCode, hc, Option.elim, claimNone, Model.nClaims]; norm_num
    | some j =>
        have := j.isLt; simp only [Model.nClaims] at this
        simp only [claimCode, hc, Option.elim]; omega
  have hbd : blockVal (runOf input env i) (Witness.bytesOf input env i)
      (decide (i < Witness.lenOf input env)) off < 2 ^ 64 := by
    rw [hb i]; split
    · exact hcc
    · simp only [claimNone, Model.nClaims]; norm_num
  rw [eval_neqU (uis_sig input env hbytes hlen hib hoff hbd) (UIs.cst (by omega)), hb i]
  by_cases hact : i < Witness.lenOf input env
  · rw [hpos i hact]
    have hd : decide (i < Witness.lenOf input env) = true := by simpa using hact
    rw [hd, Bool.true_and]
    cases hf : fld (sigOf (runOf input env i) (Witness.bytesOf input env i)) with
    | true =>
        simp only [if_true, Bool.true_and, decide_eq_decide]
        exact claimCode_eq_iff hk'
    | false =>
        simp only [Bool.false_eq_true, if_false, Bool.false_and, claimNone, Model.nClaims]
        exact decide_eq_false (by omega)
  · rw [hneg i hact]
    have hd : decide (i < Witness.lenOf input env) = false := by simpa using hact
    rw [hd, Bool.false_and]
    simp only [Bool.false_eq_true, if_false, Bool.false_and, claimNone, Model.nClaims]
    exact decide_eq_false (by omega)

/-- The tail of the cell proof: once the per-position predicate and the routed value are
identified, the fold is the model's first-match search over the active prefix. -/
theorem eval_cellE_of (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hlen : (env input.len).val ≤ bufferLen) (c : ℕ) (q : ℕ → Bool) (valOf : ℕ → ℕ)
    (hP : ∀ i ∈ List.range bufferLen,
      Witgen.BExpr.eval { env := env, locals := evalSteps env (runSteps input) }
        (.neq (sigl i sCELLIDX) (cst c)) = q i)
    (hX : ∀ i ∈ List.range bufferLen, q i = true →
      Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) }
        (.ofU64 (sigl i sVALOUT)) = ((valOf i : ℕ) : Fp))
    (hpast : ∀ i, Witness.lenOf input env ≤ i → q i = false) :
    Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) } (cellE c)
      = ((((List.range (Witness.lenOf input env)).find? q).elim 0 valOf : ℕ) : Fp) := by
  rw [cellE, eval_first_foldr _ hP hX]
  exact congrArg (fun n : ℕ => (n : Fp)) (congrArg (fun o : Option ℕ => o.elim 0 valOf)
    (find?_range_trunc _ (len := Witness.lenOf input env) (n := bufferLen) hlen hpast))

/-- The routed cell index of a position decides the model's routing test. -/
theorem cellE_pred (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) (t : ℕ) (ht : t < ofsMax) :
    ∀ i ∈ List.range bufferLen,
      Witgen.BExpr.eval { env := env, locals := evalSteps env (runSteps input) }
          (.neq (sigl i sCELLIDX) (cst (cellCode k.val t)))
        = ((Model.runSignals (Witness.bytesOf input env) (Witness.lenOf input env) i).write &&
            decide ((runOf input env i).claim = some k) &&
              decide ((runOf input env i).ofs = t)) := by
  have hk : k.val < nClaims := k.isLt
  simp only [Model.nClaims] at hk
  simp only [Model.ofsMax] at ht
  intro i hi
  have hib : i < bufferLen := List.mem_range.mp hi
  have hofs : (runOf input env i).ofs ≤ ofsMax - 1 := run_ofs_le _ _ i
  simp only [Model.ofsMax] at hofs
  have hcc : claimCode (runOf input env i).claim ≤ nClaims := by
    cases hc : (runOf input env i).claim with
    | none => simp only [claimCode, hc, Option.elim, claimNone]; exact le_refl _
    | some j =>
        have := j.isLt
        simp only [claimCode, hc, Option.elim]
        omega
  simp only [Model.nClaims] at hcc
  have hbd : blockVal (runOf input env i) (Witness.bytesOf input env i)
      (decide (i < Witness.lenOf input env)) sCELLIDX < 2 ^ 64 := by
    rw [blockVal_cellIdx]
    split
    · simp only [Model.ofsMax]; omega
    · simp only [cellNone, Model.nClaims, Model.ofsMax]; norm_num
  rw [eval_neqU (uis_sig input env hbytes hlen hib (by decide) hbd)
    (UIs.cst (by simp only [cellCode, Model.ofsMax]; omega))]
  rw [blockVal_cellIdx]
  by_cases hact : i < Witness.lenOf input env
  · rw [runSignals_write_pos hact]
    have hd : decide (i < Witness.lenOf input env) = true := by simpa using hact
    rw [hd, Bool.true_and]
    cases hf : (sigOf (runOf input env i) (Witness.bytesOf input env i)).write with
    | true =>
        simp only [if_true, Bool.true_and]
        rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
          decide_eq_true_eq, cellCode, Model.ofsMax]
        constructor
        · intro he
          have h1 : claimCode (runOf input env i).claim = k.val := by omega
          exact ⟨(claimCode_eq_iff k.isLt).mp h1, by omega⟩
        · rintro ⟨h1, h2⟩
          rw [(claimCode_eq_iff k.isLt).mpr h1, h2]
    | false =>
        simp only [Bool.false_eq_true, if_false, Bool.false_and, cellNone, cellCode,
          Model.nClaims, Model.ofsMax]
        exact decide_eq_false (by omega)
  · rw [runSignals_write_neg hact]
    have hd : decide (i < Witness.lenOf input env) = false := by simpa using hact
    rw [hd, Bool.false_and]
    simp only [Bool.false_eq_true, if_false, Bool.false_and, cellNone, cellCode,
      Model.nClaims, Model.ofsMax]
    exact decide_eq_false (by omega)

set_option maxRecDepth 40000 in
/-- At a routing position the stored value is the model's. -/
theorem cellE_valOut (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) (t : ℕ) :
    ∀ i ∈ List.range bufferLen,
      ((Model.runSignals (Witness.bytesOf input env) (Witness.lenOf input env) i).write &&
        decide ((runOf input env i).claim = some k) &&
          decide ((runOf input env i).ofs = t)) = true →
      Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) }
          (.ofU64 (sigl i sVALOUT))
        = (((Model.runSignals (Witness.bytesOf input env) (Witness.lenOf input env) i).valOut
            : ℕ) : Fp) := by
  intro i hi hq
  have hib : i < bufferLen := List.mem_range.mp hi
  have hw : (Model.runSignals (Witness.bytesOf input env)
      (Witness.lenOf input env) i).write = true := by
    simp only [Bool.and_eq_true] at hq; exact hq.1.1
  have hact : i < Witness.lenOf input env := by
    by_contra hc
    rw [runSignals_write_neg hc] at hw
    simp at hw
  have hb256 : Witness.bytesOf input env i < 256 := by
    simp only [Witness.bytesOf, dif_pos hib]; exact hbytes i hib
  have hvo : blockVal (runOf input env i) (Witness.bytesOf input env i)
      (decide (i < Witness.lenOf input env)) sVALOUT < 2 ^ 64 := by
    have := sigOf_valOut_lt (r := runOf input env i) hb256
      (show (runOf input env i).hexAcc < 4096 from run_hexAcc_lt _ _ i)
    rw [blockVal_valOut]; omega
  have hu := uis_sig input env hbytes hlen hib (off := sVALOUT) (by decide) hvo
  rw [eval_ofU64, hu.2, runSignals_valOut_pos hact,
    ← blockVal_valOut (runOf input env i) (Witness.bytesOf input env i)
      (decide (i < Witness.lenOf input env))]
  exact fromNat_ofNat hvo

theorem eval_cellE (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) (t : ℕ) (ht : t < ofsMax) :
    Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) }
        (cellE (cellCode k.val t))
      = ((Model.cell (Witness.bytesOf input env) (Witness.lenOf input env) k t : ℕ) : Fp) := by
  refine eval_cellE_of input env hlen _ _ _ (cellE_pred input env hbytes hlen k t ht)
    (cellE_valOut input env hbytes hlen k t) ?_
  intro i hi
  show ((Model.runSignals (Witness.bytesOf input env) (Witness.lenOf input env) i).write &&
    decide ((Model.run (Witness.bytesOf input env) (Witness.lenOf input env) i).claim = some k) &&
      decide ((Model.run (Witness.bytesOf input env) (Witness.lenOf input env) i).ofs = t))
    = false
  rw [runSignals_write_neg (Nat.not_lt.mpr hi)]
  simp

/-! ### Assembling the output vector -/

theorem map_cast {α β : Type} {m n : ℕ} (h : m = n) (v : Vector α m) (f : α → β) :
    (v.cast h).map f = (v.map f).cast h := by subst h; rfl

theorem eval_slotLenE (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) :
    Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) } (slotLenE k.val)
      = ((Model.slotLen (Witness.bytesOf input env) (Witness.lenOf input env) k : ℕ) : Fp) := by
  rw [slotLenE, eval_countE_of input env hlen sVEMITC k.val _
    (eval_claimCount input env hbytes hlen sVEMITC (by decide) Model.Signals.vEmit k
      (fun i => blockVal_vEmitC _ _ _) (fun i h => runSignals_vEmit_pos h)
      (fun i h => runSignals_vEmit_neg h))
    (fun i hi => by rw [runSignals_vEmit_neg (Nat.not_lt.mpr hi)]; simp)]
  simp only [Model.slotLen]

theorem eval_signE (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) :
    Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) } (signE k.val)
      = ((Model.signCount (Witness.bytesOf input env) (Witness.lenOf input env) k : ℕ) : Fp) := by
  rw [signE, eval_countE_of input env hlen sMINUSC k.val _
    (eval_claimCount input env hbytes hlen sMINUSC (by decide) Model.Signals.minusFlag k
      (fun i => blockVal_minusC _ _ _) (fun i h => runSignals_minusFlag_pos h)
      (fun i h => runSignals_minusFlag_neg h))
    (fun i hi => by rw [runSignals_minusFlag_neg (Nat.not_lt.mpr hi)]; simp)]
  simp only [Model.signCount]

theorem eval_trueE (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) :
    Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) } (trueE k.val)
      = ((Model.trueCount (Witness.bytesOf input env) (Witness.lenOf input env) k : ℕ) : Fp) := by
  rw [trueE, eval_countE_of input env hlen sTRUEC k.val _
    (eval_claimCount input env hbytes hlen sTRUEC (by decide) Model.Signals.trueDone k
      (fun i => blockVal_trueC _ _ _) (fun i h => runSignals_trueDone_pos h)
      (fun i h => runSignals_trueDone_neg h))
    (fun i hi => by rw [runSignals_trueDone_neg (Nat.not_lt.mpr hi)]; simp)]
  simp only [Model.trueCount]

theorem map_cells (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) (n : ℕ) (hn : n ≤ ofsMax) :
    (Vector.ofFn fun t : Fin n => cellE (cellCode k.val t.val)).map
        (Witgen.FExpr.eval { env := env, locals := evalSteps env (runSteps input) })
      = Witness.cellsGen (Witness.bytesOf input env) (Witness.lenOf input env) k n := by
  ext t ht
  simp only [Vector.getElem_map, Vector.getElem_ofFn, Witness.cellsGen]
  exact eval_cellE input env hbytes hlen k t (by omega)

/-! ### Struct evaluation of the read-out

`Witgen.eval` is the struct-preserving reading of a witness-IR expression struct
(`toElements`, mapped, and back through `fromElements`). Decomposing it field by
field on an *opaque* slot is what keeps the assembly of the 688-element output
vector away from the concrete `Vector.ofFn` cell folds: the leaves are closed by
the component lemmas above, never by reducing a fold. -/

theorem eval_fields {n : ℕ} (ctx : Ctx Fp) (v : Vector FE n) :
    Witgen.eval (M := fields n) ctx v = v.map (FExpr.eval ctx) := rfl

theorem toComponents_strSlot {n : ℕ} (p l : FE) (b : Vector FE n) :
    toComponents (F := FE) (α := StrSlot n) { present := p, len := l, bytes := b }
      = .cons p (.cons l (.cons b .nil)) := rfl

theorem toComponents_intSlot {n : ℕ} (p ng l : FE) (d : Vector FE n) :
    toComponents (F := FE) (α := IntSlot n)
        { present := p, negative := ng, len := l, digits := d }
      = .cons p (.cons ng (.cons l (.cons d .nil))) := rfl

theorem toComponents_boolSlot (p v : FE) :
    toComponents (F := FE) (α := BoolSlot) { present := p, value := v }
      = .cons p (.cons v .nil) := rfl

theorem eval_strSlot {n : ℕ} (ctx : Ctx Fp) (p l : FE) (b : Vector FE n) :
    Witgen.eval (M := StrSlot n) ctx { present := p, len := l, bytes := b } =
      { present := FExpr.eval ctx p, len := FExpr.eval ctx l,
        bytes := b.map (FExpr.eval ctx) } := by
  rw [Witgen.StructEval.eval_eq_eval]
  simp only [Witgen.StructEval.eval, toComponents_strSlot, components,
    Witgen.StructEval.eval.go, Witgen.eval_field, eval_fields]
  rfl

theorem eval_intSlot {n : ℕ} (ctx : Ctx Fp) (p ng l : FE) (d : Vector FE n) :
    Witgen.eval (M := IntSlot n) ctx
        { present := p, negative := ng, len := l, digits := d } =
      { present := FExpr.eval ctx p, negative := FExpr.eval ctx ng,
        len := FExpr.eval ctx l, digits := d.map (FExpr.eval ctx) } := by
  rw [Witgen.StructEval.eval_eq_eval]
  simp only [Witgen.StructEval.eval, toComponents_intSlot, components,
    Witgen.StructEval.eval.go, Witgen.eval_field, eval_fields]
  rfl

theorem eval_boolSlot (ctx : Ctx Fp) (p v : FE) :
    Witgen.eval (M := BoolSlot) ctx { present := p, value := v } =
      { present := FExpr.eval ctx p, value := FExpr.eval ctx v } := by
  rw [Witgen.StructEval.eval_eq_eval]
  simp only [Witgen.StructEval.eval, toComponents_boolSlot, components,
    Witgen.StructEval.eval.go, Witgen.eval_field]
  rfl

theorem eval_output (ctx : Ctx Fp) (x : Output FE) :
    Witgen.eval (M := Output) ctx x =
      { iss := Witgen.eval ctx x.iss, sub := Witgen.eval ctx x.sub, aud := Witgen.eval ctx x.aud,
        azp := Witgen.eval ctx x.azp, hd := Witgen.eval ctx x.hd,
        email := Witgen.eval ctx x.email, emailVerified := Witgen.eval ctx x.emailVerified,
        nonce := Witgen.eval ctx x.nonce, atHash := Witgen.eval ctx x.atHash,
        iat := Witgen.eval ctx x.iat, exp := Witgen.eval ctx x.exp } := by
  rw [Witgen.StructEval.eval_eq_eval]
  simp only [Witgen.StructEval.eval, Witgen.StructEval.eval.go]
  rfl

/-- One string slot of the read-out evaluates to `Witness.strSlotGen`. -/
theorem eval_strSlotE (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) (n : ℕ) (hn : n ≤ ofsMax) :
    Witgen.eval (M := StrSlot n) { env := env, locals := evalSteps env (runSteps input) }
        (strSlotE k.val n)
      = Witness.strSlotGen (Witness.bytesOf input env) (Witness.lenOf input env) k n := by
  simp only [strSlotE, Witness.strSlotGen]
  rw [eval_strSlot, eval_presentE input env hbytes hlen k,
    eval_slotLenE input env hbytes hlen k, map_cells input env hbytes hlen k n hn]

/-- One integer slot of the read-out evaluates to `Witness.intSlotGen`. -/
theorem eval_intSlotE (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) (n : ℕ) (hn : n ≤ ofsMax) :
    Witgen.eval (M := IntSlot n) { env := env, locals := evalSteps env (runSteps input) }
        (intSlotE k.val n)
      = Witness.intSlotGen (Witness.bytesOf input env) (Witness.lenOf input env) k n := by
  simp only [intSlotE, Witness.intSlotGen]
  rw [eval_intSlot, eval_presentE input env hbytes hlen k,
    eval_signE input env hbytes hlen k,
    eval_slotLenE input env hbytes hlen k, map_cells input env hbytes hlen k n hn]

/-- The boolean slot of the read-out evaluates to `Witness.boolSlotGen`. -/
theorem eval_boolSlotE (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) (k : Model.Claim) :
    Witgen.eval (M := BoolSlot) { env := env, locals := evalSteps env (runSteps input) }
        (boolSlotE k.val)
      = Witness.boolSlotGen (Witness.bytesOf input env) (Witness.lenOf input env) k := by
  simp only [boolSlotE, Witness.boolSlotGen]
  rw [eval_boolSlot, eval_presentE input env hbytes hlen k,
    eval_trueE input env hbytes hlen k]

/-- The whole read-out struct evaluates to the honest output of `Witness.lean`. -/
theorem eval_outStruct (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    Witgen.eval (M := Output) { env := env, locals := evalSteps env (runSteps input) } outStruct
      = Witness.outputGen (Witness.bytesOf input env) (Witness.lenOf input env) := by
  rw [eval_output]
  simp only [outStruct, Witness.outputGen, Output.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact eval_strSlotE input env hbytes hlen 0 _ (by decide)
  · exact eval_strSlotE input env hbytes hlen 1 _ (by decide)
  · exact eval_strSlotE input env hbytes hlen 2 _ (by decide)
  · exact eval_strSlotE input env hbytes hlen 3 _ (by decide)
  · exact eval_strSlotE input env hbytes hlen 4 _ (by decide)
  · exact eval_strSlotE input env hbytes hlen 5 _ (by decide)
  · exact eval_boolSlotE input env hbytes hlen 6
  · exact eval_strSlotE input env hbytes hlen 7 _ (by decide)
  · exact eval_strSlotE input env hbytes hlen 8 _ (by decide)
  · exact eval_intSlotE input env hbytes hlen 9 _ (by decide)
  · exact eval_intSlotE input env hbytes hlen 10 _ (by decide)

/-- The output program's vector is the `toElements` of the evaluated read-out struct:
`outLit` is a literal of `ProvableType.toElements outStruct`, and `Witgen.eval` is
exactly "map the field evaluation over `toElements`". -/
theorem eval_outIR_aux (input : Var Input Fp) (env : ProverEnvironment Fp) :
    (outIR input).eval env
      = ProvableType.toElements
          (Witgen.eval (M := Output)
            { env := env, locals := evalSteps env (runSteps input) } outStruct) := by
  simp only [outIR, WitgenIR.eval, outLit, Witgen.VExpr.eval, Witgen.eval,
    ProvableType.toElements_fromElements]

/-- The output read-out needs the *signal* half of a block (`write`, `valOut`, the routed
cell index and the per-claim flags), not just the registers; this is the layout half of
the bridge, assembled from the per-slot lemmas above. -/
theorem eval_outIR (input : Var Input Fp) (env : ProverEnvironment Fp)
    (hbytes : ∀ j, (h : j < bufferLen) → (env (input.buffer[j]'h)).val < 256)
    (hlen : (env input.len).val ≤ bufferLen) :
    (outIR input).eval env
      = ProvableType.toElements
          (Witness.outputGen (Witness.bytesOf input env) (Witness.lenOf input env)) :=
  (eval_outIR_aux input env).trans
    (congrArg ProvableType.toElements (eval_outStruct input env hbytes hlen))

end Bridge

attribute [irreducible] stOut subOut mOut claimOut natOut
  hexAccOut kIdxOut ofsOut nMemOut outStruct outLit
  stIR subIR mIR claimIR hexAccIR kIdxIR ofsIR nMemIR lenFlagsIR accmIR outIR

end Solution.JSONExtract.IR
