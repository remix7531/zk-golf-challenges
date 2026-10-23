import Challenge.Instances.JSONExtract.Interface
import Clean.Circuit
import Solution.JSONExtract.Model

/-!
# Honest witness of the extractor (`JSONExtract`)

The honest prover's witness for `main` is the run of the automaton of
`Model.lean` over the input buffer, projected to the register vectors `main`
witnesses (one entry per position, or per position and state/claim, flattened
position-major), plus the output slots read off the run.
-/

namespace Solution.JSONExtract.Witness

open Challenge.Instances.JSONExtract.Interface
open Model

/-- Register slots: one before each position plus the final one. -/
@[reducible] def slots : ℕ := bufferLen + 1

/-- The byte values of the input buffer under a prover environment. -/
def bytesOf (input : Var Input (F circomPrime)) (env : ProverEnvironment (F circomPrime)) :
    ℕ → ℕ :=
  fun j => if h : j < bufferLen then (env (input.buffer[j]'h)).val else 0

/-- The claimed length under a prover environment. -/
def lenOf (input : Var Input (F circomPrime)) (env : ProverEnvironment (F circomPrime)) : ℕ :=
  (env input.len).val

/-- `1` if the `Bool` holds, else `0`. -/
def ind (b : Bool) : F circomPrime := if b then 1 else 0

/-- The one-hot main state, position-major. -/
def stGen (bytes : ℕ → ℕ) (len : ℕ) : Vector (F circomPrime) (nSt * slots) :=
  Vector.ofFn fun idx => ind ((run bytes len (idx.val / nSt)).st.val = idx.val % nSt)

/-- The one-hot sub-state, position-major. -/
def subGen (bytes : ℕ → ℕ) (len : ℕ) : Vector (F circomPrime) (nSub * slots) :=
  Vector.ofFn fun idx => ind ((run bytes len (idx.val / nSub)).sub.val = idx.val % nSub)

def hexAccGen (bytes : ℕ → ℕ) (len : ℕ) : Vector (F circomPrime) slots :=
  Vector.ofFn fun i => ((run bytes len i.val).hexAcc : F circomPrime)

def kIdxGen (bytes : ℕ → ℕ) (len : ℕ) : Vector (F circomPrime) slots :=
  Vector.ofFn fun i => ((run bytes len i.val).kIdx : F circomPrime)

def ofsGen (bytes : ℕ → ℕ) (len : ℕ) : Vector (F circomPrime) slots :=
  Vector.ofFn fun i => ((run bytes len i.val).ofs : F circomPrime)

def nMemGen (bytes : ℕ → ℕ) (len : ℕ) : Vector (F circomPrime) slots :=
  Vector.ofFn fun i => ((run bytes len i.val).nMem : F circomPrime)

/-- The key matchers, position-major. -/
def mGen (bytes : ℕ → ℕ) (len : ℕ) : Vector (F circomPrime) (nClaims * slots) :=
  Vector.ofFn fun idx =>
    ind ((run bytes len (idx.val / nClaims)).m[idx.val % nClaims]'(Nat.mod_lt _ (by decide)))

/-- The claim register (one-hot, all zero for an unknown key), position-major. -/
def claimGen (bytes : ℕ → ℕ) (len : ℕ) : Vector (F circomPrime) (nClaims * slots) :=
  Vector.ofFn fun idx =>
    ind ((run bytes len (idx.val / nClaims)).claim = some ⟨idx.val % nClaims, Nat.mod_lt _ (by decide)⟩)

/-- The one-hot of `len` over the positions and the end position `bufferLen`. -/
def lenFlagsGen (len : ℕ) : Vector (F circomPrime) slots :=
  Vector.ofFn fun i => ind (i.val = len)

/-- The prefix sum of `lenFlagsGen` (`accm[i] = [len < i]`). -/
def accmGen (len : ℕ) : Vector (F circomPrime) slots :=
  Vector.ofFn fun i => ind (len < i.val)

/-! ## The output -/

/-- The zero-padded values of claim `k`'s slot. -/
def cellsGen (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) (n : ℕ) : Vector (F circomPrime) n :=
  Vector.ofFn fun t => (cell bytes len k t.val : F circomPrime)

def strSlotGen (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) (n : ℕ) : StrSlot n (F circomPrime) :=
  { present := (presentCount bytes len k : F circomPrime),
    len := (slotLen bytes len k : F circomPrime),
    bytes := cellsGen bytes len k n }

def intSlotGen (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) (n : ℕ) : IntSlot n (F circomPrime) :=
  { present := (presentCount bytes len k : F circomPrime),
    negative := (signCount bytes len k : F circomPrime),
    len := (slotLen bytes len k : F circomPrime),
    digits := cellsGen bytes len k n }

def boolSlotGen (bytes : ℕ → ℕ) (len : ℕ) (k : Claim) : BoolSlot (F circomPrime) :=
  { present := (presentCount bytes len k : F circomPrime),
    value := (trueCount bytes len k : F circomPrime) }

/-- The honest output. -/
def outputGen (bytes : ℕ → ℕ) (len : ℕ) : Output (F circomPrime) :=
  { iss := strSlotGen bytes len 0 _, sub := strSlotGen bytes len 1 _,
    aud := strSlotGen bytes len 2 _, azp := strSlotGen bytes len 3 _,
    hd := strSlotGen bytes len 4 _, email := strSlotGen bytes len 5 _,
    emailVerified := boolSlotGen bytes len 6,
    nonce := strSlotGen bytes len 7 _, atHash := strSlotGen bytes len 8 _,
    iat := intSlotGen bytes len 9 _, exp := intSlotGen bytes len 10 _ }

end Solution.JSONExtract.Witness
