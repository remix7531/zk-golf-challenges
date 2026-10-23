import Challenge.Instances.JSONExtract.Interface

/-!
# Nat-level model of the extraction automaton

The circuit in `Step.lean`/`Main.lean` checks, position by position, that a
witnessed run of an automaton over the input bytes is valid and that the run
drives the output. This file is that automaton as plain functions on `ℕ` and
`Bool`: the state spaces, the byte classes, the transition functions (`Option`,
`none` meaning "no transition", i.e. the input is rejected), the per-position
derived signals (emission, decoded code point, routing), and `run`, the honest
run over a byte buffer. The honest prover's witness is `run` projected to
vectors; the soundness proof shows the constraints force the witness to be
`run`.

Claims are indexed in the order of `Specs.JSONExtract.google.fields`:
`0 iss, 1 sub, 2 aud, 3 azp, 4 hd, 5 email, 6 email_verified, 7 nonce,
8 at_hash, 9 iat, 10 exp`.
-/

namespace Solution.JSONExtract.Model

open Specs.JSON (quote backslash slash lbrace rbrace colon comma minus plus dot
  digit0 digit9 lowerA lowerB lowerE lowerF lowerN lowerR lowerT lowerU upperA upperE upperF
  space tab lf cr backspace formfeed)

/-! ## State spaces -/

/-- Number of main automaton states. -/
@[reducible] def nSt : ℕ := 27
/-- Number of string sub-automaton states. -/
@[reducible] def nSub : ℕ := 13
/-- Number of known claims. -/
@[reducible] def nClaims : ℕ := 11
/-- Width of the key-index one-hot (`kIdx` saturates at `kIdxMax - 1`). -/
@[reducible] def kIdxMax : ℕ := 16
/-- Width of the value-offset one-hot (`ofs` saturates at `ofsMax - 1`). -/
@[reducible] def ofsMax : ℕ := 129
/-- The member cap of the schema. -/
@[reducible] def maxMembers : ℕ := Specs.JSONExtract.maxMembers

/-- Main automaton states. -/
abbrev St := Fin nSt
/-- String sub-automaton states. -/
abbrev Sub := Fin nSub
/-- A known claim index. -/
abbrev Claim := Fin nClaims

namespace St
def PRE : St := 0
def OBJ : St := 1
def KEY : St := 2
def AKEY : St := 3
def PVAL : St := 4
def STR : St := 5
def NSIGN : St := 6
def NZERO : St := 7
def NINT : St := 8
def NDOT : St := 9
def NFRAC : St := 10
def NE : St := 11
def NESIGN : St := 12
def NEXP : St := 13
def T1 : St := 14
def T2 : St := 15
def T3 : St := 16
def F1 : St := 17
def F2 : St := 18
def F3 : St := 19
def F4 : St := 20
def N1 : St := 21
def N2 : St := 22
def N3 : St := 23
def AVAL : St := 24
def SEP : St := 25
def END : St := 26
end St

namespace Sub
def PLAIN : Sub := 0
def ESC : Sub := 1
def H1 : Sub := 2
def H2 : Sub := 3
def H3 : Sub := 4
def H4 : Sub := 5
def C1 : Sub := 6
def C2 : Sub := 7
def C3 : Sub := 8
def E0s : Sub := 9
def EDs : Sub := 10
def F0s : Sub := 11
def F4s : Sub := 12
end Sub

/-! ## Byte classes -/

def isWs (b : ℕ) : Bool := b == space || b == tab || b == lf || b == cr
def isDigit (b : ℕ) : Bool := digit0 ≤ b && b ≤ digit9
def isDigitNz (b : ℕ) : Bool := digit0 < b && b ≤ digit9
def isUpperHex (b : ℕ) : Bool := upperA ≤ b && b ≤ upperF
def isLowerHex (b : ℕ) : Bool := lowerA ≤ b && b ≤ lowerF
def isHex (b : ℕ) : Bool := isDigit b || isUpperHex b || isLowerHex b
/-- A byte that may stand for itself inside a string: `0x20..0x7F` minus `"`, `\`. -/
def isUnescaped (b : ℕ) : Bool := space ≤ b && b ≤ 0x7F && b != quote && b != backslash
def isExpLetter (b : ℕ) : Bool := b == lowerE || b == upperE
def isSign (b : ℕ) : Bool := b == plus || b == minus
def isSimpleEsc (b : ℕ) : Bool :=
  b == quote || b == backslash || b == slash || b == lowerB || b == lowerF || b == lowerN ||
    b == lowerR || b == lowerT
def isCont (b : ℕ) : Bool := 0x80 ≤ b && b ≤ 0xBF
def isLead2 (b : ℕ) : Bool := 0xC2 ≤ b && b ≤ 0xDF
/-- 3-byte lead bytes without a restricted second byte. -/
def isLead3 (b : ℕ) : Bool := (0xE1 ≤ b && b ≤ 0xEC) || (0xEE ≤ b && b ≤ 0xEF)
/-- 4-byte lead bytes without a restricted second byte. -/
def isLead4 (b : ℕ) : Bool := 0xF1 ≤ b && b ≤ 0xF3
def isContA0BF (b : ℕ) : Bool := 0xA0 ≤ b && b ≤ 0xBF
def isCont809F (b : ℕ) : Bool := 0x80 ≤ b && b ≤ 0x9F
def isCont90BF (b : ℕ) : Bool := 0x90 ≤ b && b ≤ 0xBF
def isCont808F (b : ℕ) : Bool := 0x80 ≤ b && b ≤ 0x8F

/-- The code point of a simple escape `\b`. -/
def escVal (b : ℕ) : ℕ :=
  if b == quote then quote else if b == backslash then backslash
  else if b == slash then slash else if b == lowerB then backspace
  else if b == lowerF then formfeed else if b == lowerN then lf
  else if b == lowerR then cr else if b == lowerT then tab else 0

/-- The value of a hex digit (`0` off the hex range). -/
def hexVal (b : ℕ) : ℕ :=
  if isDigit b then b - digit0 else if isUpperHex b then b - upperA + 10
  else if isLowerHex b then b - lowerA + 10 else 0

/-- The marker emitted for a raw UTF-8 sequence: not ASCII, value irrelevant. -/
@[reducible] def nonAsciiMarker : ℕ := 0x80

/-! ## Claims -/

/-- The name of claim `k` as bytes. -/
def claimName (k : Claim) : List ℕ :=
  (Specs.JSONExtract.google.fields.map (·.name)).getD k.val []

/-- A value no code point can equal (`\uXXXX` gives at most `0xFFFF`). -/
@[reducible] def impossible : ℕ := 2 ^ 20

/-- Every claim name fits below the saturation index of `kIdx`. -/
theorem claimName_length_lt : ∀ k : Claim, (claimName k).length < kIdxMax := by decide

/-- The `t`-th byte of the name of claim `k`, `impossible` past its end. -/
def nameAt (k : Claim) (t : ℕ) : ℕ := (claimName k).getD t impossible

/-- Cap (cells) of the output slot of claim `k`. -/
def claimCap (k : Claim) : ℕ :=
  match Specs.JSONExtract.google.fields.getD k.val ⟨[], .bool⟩ |>.spec with
  | .str n => n
  | .int n => n
  | .bool => 0

def isStrClaim (k : Claim) : Bool :=
  match Specs.JSONExtract.google.fields.getD k.val ⟨[], .bool⟩ |>.spec with
  | .str _ => true | _ => false
def isIntClaim (k : Claim) : Bool :=
  match Specs.JSONExtract.google.fields.getD k.val ⟨[], .bool⟩ |>.spec with
  | .int _ => true | _ => false
def isBoolClaim (k : Claim) : Bool :=
  match Specs.JSONExtract.google.fields.getD k.val ⟨[], .bool⟩ |>.spec with
  | .bool => true | _ => false

/-- The kind of the value being read: the claim's type, or unknown. -/
inductive Kind where
  | str | int | bool | unk
deriving DecidableEq, Repr

def kindOf : Option Claim → Kind
  | none => .unk
  | some k => if isStrClaim k then .str else if isIntClaim k then .int else .bool

/-! ## Transitions -/

/-- The sub-automaton step. `inStr` says the main automaton is inside a string
    (`KEY` or `STR`); outside strings the sub-state is forced to `PLAIN` and the
    byte is not inspected. `none` is a rejection. -/
def stepSub (inStr : Bool) (s : Sub) (b : ℕ) : Option Sub :=
  if !inStr then some Sub.PLAIN
  else if s = Sub.PLAIN then
    if b == quote then some Sub.PLAIN
    else if isUnescaped b then some Sub.PLAIN
    else if b == backslash then some Sub.ESC
    else if isLead2 b then some Sub.C1
    else if b == 0xE0 then some Sub.E0s
    else if isLead3 b then some Sub.C2
    else if b == 0xED then some Sub.EDs
    else if b == 0xF0 then some Sub.F0s
    else if isLead4 b then some Sub.C3
    else if b == 0xF4 then some Sub.F4s
    else none
  else if s = Sub.ESC then
    if isSimpleEsc b then some Sub.PLAIN else if b == lowerU then some Sub.H1 else none
  else if s = Sub.H1 then if isHex b then some Sub.H2 else none
  else if s = Sub.H2 then if isHex b then some Sub.H3 else none
  else if s = Sub.H3 then if isHex b then some Sub.H4 else none
  else if s = Sub.H4 then if isHex b then some Sub.PLAIN else none
  else if s = Sub.C1 then if isCont b then some Sub.PLAIN else none
  else if s = Sub.C2 then if isCont b then some Sub.C1 else none
  else if s = Sub.C3 then if isCont b then some Sub.C2 else none
  else if s = Sub.E0s then if isContA0BF b then some Sub.C1 else none
  else if s = Sub.EDs then if isCont809F b then some Sub.C1 else none
  else if s = Sub.F0s then if isCont90BF b then some Sub.C2 else none
  else if isCont808F b then some Sub.C2 else none   -- F4s

/-- The common tail of a value: whitespace, `,` or `}`. -/
def afterValue (b : ℕ) : Option St :=
  if isWs b then some St.AVAL else if b == comma then some St.SEP
  else if b == rbrace then some St.END else none

/-- The main automaton step. `subPlain` says the sub-state before the byte is
    `PLAIN` (so a `"` closes the string); `kind` is the type gate of the value
    being read. `none` is a rejection. -/
def stepSt (kind : Kind) (subPlain : Bool) (s : St) (b : ℕ) : Option St :=
  if s = St.PRE then if isWs b then some St.PRE else if b == lbrace then some St.OBJ else none
  else if s = St.OBJ then
    if isWs b then some St.OBJ else if b == quote then some St.KEY
    else if b == rbrace then some St.END else none
  else if s = St.KEY then if b == quote && subPlain then some St.AKEY else some St.KEY
  else if s = St.AKEY then if isWs b then some St.AKEY else if b == colon then some St.PVAL else none
  else if s = St.PVAL then
    if isWs b then some St.PVAL
    else if b == quote && (kind = .str || kind = .unk) then some St.STR
    else if b == minus && (kind = .int || kind = .unk) then some St.NSIGN
    else if b == digit0 && (kind = .int || kind = .unk) then some St.NZERO
    else if isDigitNz b && (kind = .int || kind = .unk) then some St.NINT
    else if b == lowerT && (kind = .bool || kind = .unk) then some St.T1
    else if b == lowerF && (kind = .bool || kind = .unk) then some St.F1
    else if b == lowerN && kind = .unk then some St.N1
    else none
  else if s = St.STR then if b == quote && subPlain then some St.AVAL else some St.STR
  else if s = St.NSIGN then
    if b == digit0 then some St.NZERO else if isDigitNz b then some St.NINT else none
  else if s = St.NZERO then
    if b == dot && kind = .unk then some St.NDOT
    else if isExpLetter b && kind = .unk then some St.NE else afterValue b
  else if s = St.NINT then
    if isDigit b then some St.NINT
    else if b == dot && kind = .unk then some St.NDOT
    else if isExpLetter b && kind = .unk then some St.NE else afterValue b
  else if s = St.NDOT then if isDigit b then some St.NFRAC else none
  else if s = St.NFRAC then
    if isDigit b then some St.NFRAC else if isExpLetter b then some St.NE else afterValue b
  else if s = St.NE then
    if isSign b then some St.NESIGN else if isDigit b then some St.NEXP else none
  else if s = St.NESIGN then if isDigit b then some St.NEXP else none
  else if s = St.NEXP then if isDigit b then some St.NEXP else afterValue b
  else if s = St.T1 then if b == lowerR then some St.T2 else none
  else if s = St.T2 then if b == lowerU then some St.T3 else none
  else if s = St.T3 then if b == lowerE then some St.AVAL else none
  else if s = St.F1 then if b == lowerA then some St.F2 else none
  else if s = St.F2 then if b == 0x6C then some St.F3 else none
  else if s = St.F3 then if b == 0x73 then some St.F4 else none
  else if s = St.F4 then if b == lowerE then some St.AVAL else none
  else if s = St.N1 then if b == lowerU then some St.N2 else none
  else if s = St.N2 then if b == 0x6C then some St.N3 else none
  else if s = St.N3 then if b == 0x6C then some St.AVAL else none
  else if s = St.AVAL then afterValue b
  else if s = St.SEP then if isWs b then some St.SEP else if b == quote then some St.KEY else none
  else if isWs b then some St.END else none   -- END

/-! ## Registers and the per-position signals -/

/-- The automaton state before a position: main state, sub-state and the
    registers. -/
structure Regs where
  st : St
  sub : Sub
  /-- accumulator of the first three hex digits of a `\uXXXX` escape -/
  hexAcc : ℕ
  /-- code points emitted so far in the current key (saturating at 15) -/
  kIdx : ℕ
  /-- per-claim key matchers: the key so far is a prefix of the claim's name -/
  m : Vector Bool nClaims
  /-- the claim whose value is being read, if the current member's key is known -/
  claim : Option Claim
  /-- values emitted so far in the current value (saturating at 128) -/
  ofs : ℕ
  /-- number of members started -/
  nMem : ℕ
deriving Repr

/-- The initial state. -/
def Regs.init : Regs :=
  { st := St.PRE, sub := Sub.PLAIN, hexAcc := 0, kIdx := 0, m := Vector.replicate nClaims false,
    claim := none, ofs := 0, nMem := 0 }

/-- Everything the circuit derives at one position from the state before it
    and the byte. -/
structure Signals where
  /-- the byte completes a code point of a string -/
  emit : Bool
  /-- the emitted code point (`0` when nothing is emitted) -/
  cp : ℕ
  hexVal : ℕ
  keyStart : Bool
  keyClose : Bool
  /-- the closing key is the name of claim `k` -/
  match_ : Vector Bool nClaims
  /-- a value (string code point or integer digit) is emitted -/
  vEmit : Bool
  digitEmit : Bool
  /-- the emitted value is routed to a known string/int claim's slot -/
  write : Bool
  /-- the routed value -/
  valOut : ℕ
  minusFlag : Bool
  trueDone : Bool
deriving Repr

def inStr (s : St) : Bool := s = St.KEY || s = St.STR

/-- The signals at a position with state `r` before the byte `b` and successor
    main state `st'` (needed for `keyStart`). -/
def signals (r : Regs) (b : ℕ) (st' : St) : Signals :=
  let strNow := inStr r.st
  let emitPlain := strNow && r.sub = Sub.PLAIN && isUnescaped b
  let emitEsc := strNow && r.sub = Sub.ESC && isSimpleEsc b
  let emitU := strNow && r.sub = Sub.H4 && isHex b
  let emitUtf8 := strNow && r.sub = Sub.C1 && isCont b
  let emit := emitPlain || emitEsc || emitU || emitUtf8
  let hv := hexVal b
  let cp := if emitPlain then b else if emitEsc then escVal b
    else if emitU then 16 * r.hexAcc + hv else if emitUtf8 then nonAsciiMarker else 0
  let keyStart := st' = St.KEY && r.st ≠ St.KEY
  let keyClose := r.st = St.KEY && b == quote && r.sub = Sub.PLAIN
  let match_ := Vector.ofFn fun k : Claim =>
    keyClose && r.m[k] && r.kIdx = (claimName k).length
  let strEmit := emit && r.st = St.STR
  let digitEmit := isDigit b && (r.st = St.PVAL || r.st = St.NSIGN || r.st = St.NINT)
  let vEmit := strEmit || digitEmit
  let kind := kindOf r.claim
  let write := vEmit && (kind = .str || kind = .int)
  let valOut := if strEmit then cp else if digitEmit then b - digit0 else 0
  { emit, cp, hexVal := hv, keyStart, keyClose, match_, vEmit, digitEmit, write, valOut,
    minusFlag := r.st = St.PVAL && b == minus,
    trueDone := r.st = St.T3 && b == lowerE }

/-- One step of the automaton on byte `b`: the next state, or `none` if the
    byte is rejected (no transition, a routed value past its slot's cap, or a
    non-ASCII code point in a known string claim). -/
def step (r : Regs) (b : ℕ) : Option Regs := do
  let sub' ← stepSub (inStr r.st) r.sub b
  let st' ← stepSt (kindOf r.claim) (r.sub = Sub.PLAIN) r.st b
  let sg := signals r b st'
  -- routing checks: a routed value must fit its slot, and a string claim's code
  -- point must be ASCII
  let capOk := !sg.write || (match r.claim with | some k => r.ofs < claimCap k | none => true)
  let asciiOk := !(sg.write && r.st = St.STR) || sg.cp < 0x80
  if !(capOk && asciiOk) then none else
  let hexAcc' := if r.sub = Sub.H1 || r.sub = Sub.H2 || r.sub = Sub.H3 then 16 * r.hexAcc + sg.hexVal else 0
  let kIdx' := if r.st = St.KEY then min (r.kIdx + (if sg.emit then 1 else 0)) (kIdxMax - 1) else 0
  let m' := Vector.ofFn fun k : Claim =>
    if sg.keyStart then true
    else if r.st = St.KEY then r.m[k] && (!sg.emit || sg.cp = nameAt k r.kIdx)
    else false
  let claim' :=
    if sg.keyClose then (List.finRange nClaims).find? fun k => sg.match_[k]
    else if sg.keyStart then none else r.claim
  let inVal := r.st ≠ St.PRE && r.st ≠ St.OBJ && r.st ≠ St.KEY && r.st ≠ St.AKEY &&
    r.st ≠ St.PVAL && r.st ≠ St.AVAL && r.st ≠ St.SEP && r.st ≠ St.END
  let ofs' := (if inVal then r.ofs else 0) + (if sg.vEmit then 1 else 0)
  let ofs' := min ofs' (ofsMax - 1)
  let nMem' := r.nMem + (if sg.keyStart then 1 else 0)
  pure { st := st', sub := sub', hexAcc := hexAcc', kIdx := kIdx', m := m', claim := claim',
         ofs := ofs', nMem := nMem' }

/-! ## The honest run -/

/-- The state before position `i` of the honest run over `bytes`, of which the
    first `len` are active: a rejected byte leaves the state unchanged (the
    honest prover never hits one on a valid input), and positions past `len`
    are frozen. -/
def run (bytes : ℕ → ℕ) (len : ℕ) : ℕ → Regs
  | 0 => Regs.init
  | i + 1 =>
    let r := run bytes len i
    if i < len then (step r (bytes i)).getD r else r

/-- The signals of the honest run at position `i` (all-off past `len`). -/
def runSignals (bytes : ℕ → ℕ) (len : ℕ) (i : ℕ) : Signals :=
  if i < len then
    let r := run bytes len i
    signals r (bytes i) ((step r (bytes i)).getD r).st
  else
    { emit := false, cp := 0, hexVal := 0, keyStart := false, keyClose := false,
      match_ := Vector.replicate nClaims false, vEmit := false, digitEmit := false,
      write := false, valOut := 0, minusFlag := false, trueDone := false }

/-- The number of members whose key is claim `k`. -/
def presentCount (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) : ℕ :=
  ((List.range len).filter fun i => (runSignals bytes len i).match_[k]).length

/-- The honest run accepts: every active byte had a transition, the final
    state is `END` with the sub-state `PLAIN`, at most `maxMembers` members
    were started, and no known key occurs twice. -/
def accepts (bytes : ℕ → ℕ) (len : ℕ) : Bool :=
  (List.range len).all (fun i => (step (run bytes len i) (bytes i)).isSome) &&
  (run bytes len len).st = St.END && (run bytes len len).sub = Sub.PLAIN &&
  (run bytes len len).nMem ≤ maxMembers &&
  (List.finRange nClaims).all fun k => presentCount bytes len k ≤ 1

/-! ## The extracted slots of the honest run -/

/-- The value routed to cell `t` of claim `k`'s slot (`0` if none). -/
def cell (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) (t : ℕ) : ℕ :=
  ((List.range len).find? fun i =>
    let r := run bytes len i
    let sg := runSignals bytes len i
    sg.write && r.claim = some k && r.ofs = t).elim 0 fun i => (runSignals bytes len i).valOut

/-- The number of values routed to claim `k`. -/
def slotLen (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) : ℕ :=
  ((List.range len).filter fun i =>
    (runSignals bytes len i).vEmit && (run bytes len i).claim = some k).length

/-- The sign of an integer claim (`1` if a `-` was consumed for it). -/
def signCount (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) : ℕ :=
  ((List.range len).filter fun i =>
    (runSignals bytes len i).minusFlag && (run bytes len i).claim = some k).length

/-- The boolean claim's value (`1` if its literal was `true`). -/
def trueCount (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) : ℕ :=
  ((List.range len).filter fun i =>
    (runSignals bytes len i).trueDone && (run bytes len i).claim = some k).length

end Solution.JSONExtract.Model
