import Mathlib.Data.List.Basic

/-!
# A minimal parser-combinator library over byte lists

Specifications in this repository parse byte strings given as `List ℕ` (every
element is meant to be a byte, `< 256`; the boundary predicates live with the
challenge interfaces). This file provides a small, proof-friendly combinator
library on top of which a grammar can be written declaratively, so that the
grammar of a spec is separated from the parsing plumbing.

A `Parser α` consumes a prefix of the input and returns the parsed value with
the remainder, or `none` on failure. There is no notion of "consumed input" for
error recovery: `<|>` simply tries the right alternative from the same position
when the left one fails. The grammars we specify are LL(1) and every choice
inspects the head byte, so this simple semantics is exactly what is wanted.

Repetition is bounded: `manyUpTo n p` parses at most `n` items and `sepByUpTo n`
at most `n` separated items. The bounds are part of the grammar (the length caps
a circuit implements), and they also give structural termination, so no fuel is
needed anywhere.

## Proof toolkit

Every combinator comes with an equation lemma stating how it evaluates on an
input, plus the two directions a round-trip proof needs:

* `*_append`: on an input of the form `token ++ rest` the combinator succeeds
  with remainder `rest` (used to show a serialization parses);
* `*_inv`: if the combinator succeeds, the input decomposes as the consumed
  tokens followed by the remainder (used to show a parse is a serialization).
-/

namespace Specs

/-- A parser over byte lists: consumes a prefix of the input, returns the
    parsed value and the remainder, or `none` on failure. -/
def Parser (α : Type) : Type := List ℕ → Option (α × List ℕ)

namespace Parser

variable {α β : Type}

/-! ## Monad structure -/

/-- Succeed without consuming input. -/
protected def pure (a : α) : Parser α := fun l => some (a, l)

/-- Sequence two parsers, feeding the remainder of the first to the second. -/
protected def bind (p : Parser α) (f : α → Parser β) : Parser β :=
  fun l => (p l).bind fun ar => f ar.1 ar.2

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

/-- Always fail. -/
def fail : Parser α := fun _ => none

/-- Try `p`; if it fails, try `q` from the same position. -/
def orElse (p q : Parser α) : Parser α :=
  fun l => match p l with
    | some r => some r
    | none => q l

instance : Alternative Parser where
  failure := fail
  orElse p q := orElse p (q ())

/-! ## Primitive parsers -/

/-- Consume one byte satisfying `p`. -/
def satisfy (p : ℕ → Bool) : Parser ℕ :=
  fun l => match l with
    | c :: r => if p c then some (c, r) else none
    | [] => none

/-- Consume exactly the byte `b`. -/
def byte (b : ℕ) : Parser Unit :=
  fun l => match l with
    | c :: r => if c = b then some ((), r) else none
    | [] => none

/-- Succeed only at the end of the input. -/
def eof : Parser Unit :=
  fun l => match l with
    | [] => some ((), [])
    | _ :: _ => none

/-- Succeed (without consuming) unless the next byte satisfies `p`. -/
def notFollowedBy (p : ℕ → Bool) : Parser Unit :=
  fun l => match l with
    | c :: _ => if p c then none else some ((), l)
    | [] => some ((), [])

/-- Drop the longest prefix of bytes satisfying `p`. Never fails. -/
def skipWhile (p : ℕ → Bool) : Parser Unit :=
  fun l => some ((), l.dropWhile p)

/-! ## Derived combinators -/

/-- Try `p`, returning `none` (without consuming) if it fails. -/
def optional (p : Parser α) : Parser (Option α) :=
  orElse (Option.some <$> p) (pure none)

/-- Greedily parse `p` as many times as it succeeds, but at most `n` times.
    Never fails. -/
def manyUpTo : ℕ → Parser α → Parser (List α)
  | 0, _ => pure []
  | n + 1, p => orElse (do let a ← p; let as ← manyUpTo n p; pure (a :: as)) (pure [])

/-- Zero or more `p`, separated by `sep`, at most `n` items. Choice is
    committed after a separator: if `sep` succeeds and the following `p` fails,
    the list stops *before* that separator (so the caller's closing token then
    fails on the separator). Never fails. -/
def sepByUpTo : ℕ → Parser α → Parser Unit → Parser (List α)
  | 0, _, _ => pure []
  | n + 1, p, sep =>
    orElse (do let a ← p; let as ← manyUpTo n (sep *> p); pure (a :: as)) (pure [])

/-- Consume exactly the byte sequence `bs`. -/
def literal : List ℕ → Parser Unit
  | [] => pure ()
  | b :: bs => byte b *> literal bs

/-- Unbounded greedy repetition of a *consuming* parser. Each success of `p`
    consumes at least one byte, so the input length bounds the number of
    iterations; this is `manyUpTo` with that bound. Never fails. -/
def many (p : Parser α) : Parser (List α) := fun l => manyUpTo l.length p l

/-- Unbounded `sepByUpTo` for a consuming `p` (same bound as `many`). Choice
    is committed after a separator, as in `sepByUpTo`. Never fails. -/
def sepBy (p : Parser α) (sep : Parser Unit) : Parser (List α) :=
  fun l => sepByUpTo l.length p sep l

/-! ## Equation lemmas -/

@[simp] theorem pure_apply (a : α) (l : List ℕ) : (pure a : Parser α) l = some (a, l) := rfl

@[simp] theorem bind_apply (p : Parser α) (f : α → Parser β) (l : List ℕ) :
    (p >>= f) l = (p l).bind fun ar => f ar.1 ar.2 := rfl

@[simp] theorem map_apply (f : α → β) (p : Parser α) (l : List ℕ) :
    (f <$> p) l = (p l).map fun ar => (f ar.1, ar.2) := by
  show ((p l).bind fun ar => some (f ar.1, ar.2)) = _
  cases p l with
  | none => rfl
  | some ar => rfl

@[simp] theorem seqRight_apply (p : Parser α) (q : Parser β) (l : List ℕ) :
    (p *> q) l = (p l).bind fun ar => q ar.2 := by
  show ((p l).bind fun ar => q ar.2) = _
  rfl

@[simp] theorem seqLeft_apply (p : Parser α) (q : Parser β) (l : List ℕ) :
    (p <* q) l = (p l).bind fun ar => (q ar.2).map fun br => (ar.1, br.2) := by
  show ((p l).bind fun ar => (q ar.2).bind fun br => some (ar.1, br.2)) = _
  cases p l with
  | none => rfl
  | some ar =>
    show ((q ar.2).bind fun br => some (ar.1, br.2)) = (q ar.2).map fun br => (ar.1, br.2)
    cases q ar.2 with
    | none => rfl
    | some br => rfl

@[simp] theorem fail_apply (l : List ℕ) : (fail : Parser α) l = none := rfl

@[simp] theorem failure_apply (l : List ℕ) : (failure : Parser α) l = none := rfl

theorem orElse_apply (p q : Parser α) (l : List ℕ) :
    orElse p q l = match p l with | some r => some r | none => q l := rfl

@[simp] theorem orElse_apply_of_some {p : Parser α} {l : List ℕ} {r : α × List ℕ}
    (h : p l = some r) (q : Parser α) : orElse p q l = some r := by
  simp [orElse_apply, h]

@[simp] theorem orElse_apply_of_none {p : Parser α} {l : List ℕ} (h : p l = none)
    (q : Parser α) : orElse p q l = q l := by
  simp [orElse_apply, h]

@[simp] theorem alt_apply (p q : Parser α) (l : List ℕ) : (p <|> q) l = orElse p q l := rfl

@[simp] theorem satisfy_nil (p : ℕ → Bool) : satisfy p [] = none := rfl

@[simp] theorem satisfy_cons (p : ℕ → Bool) (c : ℕ) (r : List ℕ) :
    satisfy p (c :: r) = if p c then some (c, r) else none := rfl

@[simp] theorem byte_nil (b : ℕ) : byte b [] = none := rfl

@[simp] theorem byte_cons (b c : ℕ) (r : List ℕ) :
    byte b (c :: r) = if c = b then some ((), r) else none := rfl

@[simp] theorem byte_cons_self (b : ℕ) (r : List ℕ) : byte b (b :: r) = some ((), r) := by
  simp

@[simp] theorem eof_nil : eof [] = some ((), []) := rfl

@[simp] theorem eof_cons (c : ℕ) (r : List ℕ) : eof (c :: r) = none := rfl

@[simp] theorem notFollowedBy_nil (p : ℕ → Bool) : notFollowedBy p [] = some ((), []) := rfl

@[simp] theorem notFollowedBy_cons (p : ℕ → Bool) (c : ℕ) (r : List ℕ) :
    notFollowedBy p (c :: r) = if p c then none else some ((), c :: r) := rfl

@[simp] theorem skipWhile_apply (p : ℕ → Bool) (l : List ℕ) :
    skipWhile p l = some ((), l.dropWhile p) := rfl

theorem optional_apply (p : Parser α) (l : List ℕ) :
    optional p l = match p l with
      | some (a, r) => some (some a, r)
      | none => some (none, l) := by
  unfold optional
  cases h : p l with
  | none => simp [h]
  | some ar => obtain ⟨a, r⟩ := ar; simp [h]

@[simp] theorem optional_apply_of_some {p : Parser α} {l : List ℕ} {a : α} {r : List ℕ}
    (h : p l = some (a, r)) : optional p l = some (some a, r) := by
  simp [optional_apply, h]

@[simp] theorem optional_apply_of_none {p : Parser α} {l : List ℕ} (h : p l = none) :
    optional p l = some (none, l) := by
  simp [optional_apply, h]

@[simp] theorem manyUpTo_zero (p : Parser α) (l : List ℕ) : manyUpTo 0 p l = some ([], l) := rfl

theorem manyUpTo_succ (n : ℕ) (p : Parser α) (l : List ℕ) :
    manyUpTo (n + 1) p l = match p l with
      | none => some ([], l)
      | some (a, r) => (manyUpTo n p r).map fun asr => (a :: asr.1, asr.2) := by
  have hsome : ∀ (m : ℕ) (l : List ℕ), (manyUpTo m p l).isSome := by
    intro m l
    cases m with
    | zero => simp
    | succ m => simp only [manyUpTo, orElse_apply]; split <;> simp
  simp only [manyUpTo, orElse_apply, bind_apply, pure_apply]
  cases h : p l with
  | none => rfl
  | some ar =>
    obtain ⟨a, r⟩ := ar
    have hr := hsome n r
    simp only [Option.bind_some]
    cases hm : manyUpTo n p r with
    | none => rw [hm] at hr; simp at hr
    | some asr => rfl

/-- `manyUpTo` never fails. -/
theorem manyUpTo_isSome (n : ℕ) (p : Parser α) (l : List ℕ) : (manyUpTo n p l).isSome := by
  cases n with
  | zero => simp
  | succ n => simp only [manyUpTo, orElse_apply]; split <;> simp

@[simp] theorem manyUpTo_succ_of_none {p : Parser α} {l : List ℕ} (h : p l = none) (n : ℕ) :
    manyUpTo (n + 1) p l = some ([], l) := by
  simp [manyUpTo_succ, h]

@[simp] theorem manyUpTo_succ_of_some {p : Parser α} {l : List ℕ} {a : α} {r : List ℕ}
    (h : p l = some (a, r)) (n : ℕ) :
    manyUpTo (n + 1) p l = (manyUpTo n p r).map fun asr => (a :: asr.1, asr.2) := by
  simp [manyUpTo_succ, h]

@[simp] theorem sepByUpTo_zero (p : Parser α) (sep : Parser Unit) (l : List ℕ) :
    sepByUpTo 0 p sep l = some ([], l) := rfl

theorem sepByUpTo_succ (n : ℕ) (p : Parser α) (sep : Parser Unit) (l : List ℕ) :
    sepByUpTo (n + 1) p sep l = match p l with
      | none => some ([], l)
      | some (a, r) => (manyUpTo n (sep *> p) r).map fun asr => (a :: asr.1, asr.2) := by
  simp only [sepByUpTo, orElse_apply, bind_apply, pure_apply]
  cases h : p l with
  | none => rfl
  | some ar =>
    obtain ⟨a, r⟩ := ar
    have hr := manyUpTo_isSome n (sep *> p) r
    simp only [Option.bind_some]
    cases hm : manyUpTo n (sep *> p) r with
    | none => rw [hm] at hr; simp at hr
    | some asr => rfl

/-- `sepByUpTo` never fails. -/
theorem sepByUpTo_isSome (n : ℕ) (p : Parser α) (sep : Parser Unit) (l : List ℕ) :
    (sepByUpTo n p sep l).isSome := by
  cases n with
  | zero => simp
  | succ n => simp only [sepByUpTo, orElse_apply]; split <;> simp

/-! ## Round-trip lemmas for repetition -/

/-- A parser `p` "tokenizes" a list `toks` with values `as` when, from every
    suffix position, `p` consumes exactly the next token. Concretely: given a
    list of `(value, token)` pairs, `p (tok ++ rest) = some (a, rest)` for every
    `rest` (the token is self-delimiting). -/
def Tokenizes (p : Parser α) (items : List (α × List ℕ)) : Prop :=
  ∀ it ∈ items, ∀ rest, p (it.2 ++ rest) = some (it.1, rest)

/-- `manyUpTo` over a run of self-delimiting tokens, followed by a `rest` on
    which `p` fails, consumes exactly the tokens. -/
theorem manyUpTo_append {p : Parser α} {items : List (α × List ℕ)} {rest : List ℕ}
    (hitems : Tokenizes p items) (hstop : p rest = none) {n : ℕ} (hn : items.length ≤ n) :
    manyUpTo n p ((items.map (·.2)).flatten ++ rest) = some (items.map (·.1), rest) := by
  induction items generalizing n with
  | nil =>
    cases n with
    | zero => simp
    | succ n => simp [hstop]
  | cons it items ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have hit := hitems it (List.mem_cons_self ..) ((items.map (·.2)).flatten ++ rest)
      have htl : Tokenizes p items := fun x hx => hitems x (List.mem_cons_of_mem _ hx)
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]
      rw [manyUpTo_succ_of_some hit, ih htl (by simpa using hn)]
      rfl

@[simp] theorem literal_nil (l : List ℕ) : literal [] l = some ((), l) := rfl

theorem literal_cons (b : ℕ) (bs : List ℕ) (l : List ℕ) :
    literal (b :: bs) l = (byte b l).bind fun ur => literal bs ur.2 := rfl

@[simp] theorem many_apply (p : Parser α) (l : List ℕ) : many p l = manyUpTo l.length p l := rfl

@[simp] theorem sepBy_apply (p : Parser α) (sep : Parser Unit) (l : List ℕ) :
    sepBy p sep l = sepByUpTo l.length p sep l := rfl

/-! ## Well-behaved parsers

An arbitrary function of type `Parser α` may return a remainder that is not a
suffix of its input. Every primitive in this file does return a suffix, and the
property is closed under all the combinators, so grammars built from them are
`Suffixing`. Inversion lemmas assume it. -/

/-- A parser is suffixing when a successful parse leaves a suffix of the input
    as the remainder: the input is the consumed token followed by the remainder. -/
def Suffixing (p : Parser α) : Prop :=
  ∀ l a r, p l = some (a, r) → ∃ tok, l = tok ++ r

theorem suffixing_pure (a : α) : Suffixing (pure a : Parser α) := by
  intro l a' r h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨[], by simp [h.2]⟩

theorem suffixing_fail : Suffixing (fail : Parser α) := by
  intro l a r h; simp at h

theorem suffixing_bind {p : Parser α} {f : α → Parser β} (hp : Suffixing p)
    (hf : ∀ a, Suffixing (f a)) : Suffixing (p >>= f) := by
  intro l b r h
  simp only [bind_apply, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r1⟩, h1, h2⟩ := h
  obtain ⟨t1, ht1⟩ := hp l a r1 h1
  obtain ⟨t2, ht2⟩ := hf a r1 b r h2
  exact ⟨t1 ++ t2, by rw [ht1, ht2, List.append_assoc]⟩

theorem suffixing_map {p : Parser α} (f : α → β) (hp : Suffixing p) : Suffixing (f <$> p) := by
  intro l b r h
  simp only [map_apply, Option.map_eq_some_iff] at h
  obtain ⟨⟨a, r1⟩, h1, h2⟩ := h
  simp only [Prod.mk.injEq] at h2
  obtain ⟨_, rfl⟩ := h2
  exact hp l a _ h1

theorem suffixing_seqRight {p : Parser α} {q : Parser β} (hp : Suffixing p) (hq : Suffixing q) :
    Suffixing (p *> q) := by
  intro l b r h
  simp only [seqRight_apply, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r1⟩, h1, h2⟩ := h
  obtain ⟨t1, ht1⟩ := hp l a r1 h1
  obtain ⟨t2, ht2⟩ := hq r1 b r h2
  exact ⟨t1 ++ t2, by rw [ht1, ht2, List.append_assoc]⟩

theorem suffixing_seqLeft {p : Parser α} {q : Parser β} (hp : Suffixing p) (hq : Suffixing q) :
    Suffixing (p <* q) := by
  intro l a r h
  simp only [seqLeft_apply, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨a1, r1⟩, h1, ⟨b, r2⟩, h2, h3⟩ := h
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨t1, ht1⟩ := hp l a1 r1 h1
  obtain ⟨t2, ht2⟩ := hq r1 b r2 h2
  exact ⟨t1 ++ t2, by rw [ht1, ht2, List.append_assoc]⟩

theorem suffixing_orElse {p q : Parser α} (hp : Suffixing p) (hq : Suffixing q) :
    Suffixing (orElse p q) := by
  intro l a r h
  rw [orElse_apply] at h
  cases hpl : p l with
  | none => rw [hpl] at h; exact hq l a r h
  | some ar => rw [hpl] at h; simp only [Option.some.injEq] at h; subst h; exact hp l _ _ hpl

theorem suffixing_alt {p q : Parser α} (hp : Suffixing p) (hq : Suffixing q) :
    Suffixing (p <|> q) := suffixing_orElse hp hq

theorem suffixing_satisfy (q : ℕ → Bool) : Suffixing (satisfy q) := by
  intro l a r h
  cases l with
  | nil => simp at h
  | cons c t =>
    simp only [satisfy_cons] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨[c], by simp [h.2]⟩
    · simp at h

theorem suffixing_byte (b : ℕ) : Suffixing (byte b) := by
  intro l a r h
  cases l with
  | nil => simp at h
  | cons c t =>
    simp only [byte_cons] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨[c], by simp [h.2]⟩
    · simp at h

theorem suffixing_eof : Suffixing eof := by
  intro l a r h
  cases l with
  | nil => simp only [eof_nil, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨[], by simp [h.2]⟩
  | cons c t => simp at h

theorem suffixing_notFollowedBy (q : ℕ → Bool) : Suffixing (notFollowedBy q) := by
  intro l a r h
  cases l with
  | nil => simp only [notFollowedBy_nil, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨[], by simp [h.2]⟩
  | cons c t =>
    simp only [notFollowedBy_cons] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨[], by simp [h.2]⟩

theorem suffixing_skipWhile (q : ℕ → Bool) : Suffixing (skipWhile q) := by
  intro l a r h
  simp only [skipWhile_apply, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨l.takeWhile q, by rw [← h.2, List.takeWhile_append_dropWhile]⟩

theorem suffixing_optional {p : Parser α} (hp : Suffixing p) : Suffixing (optional p) :=
  suffixing_orElse (suffixing_map _ hp) (suffixing_pure _)

theorem suffixing_manyUpTo {p : Parser α} (hp : Suffixing p) (n : ℕ) : Suffixing (manyUpTo n p) := by
  induction n with
  | zero => exact suffixing_pure _
  | succ n ih =>
    exact suffixing_orElse
      (suffixing_bind hp fun _ => suffixing_bind ih fun _ => suffixing_pure _)
      (suffixing_pure _)

theorem suffixing_sepByUpTo {p : Parser α} {sep : Parser Unit} (hp : Suffixing p)
    (hsep : Suffixing sep) (n : ℕ) : Suffixing (sepByUpTo n p sep) := by
  cases n with
  | zero => exact suffixing_pure _
  | succ n =>
    exact suffixing_orElse
      (suffixing_bind hp fun _ =>
        suffixing_bind (suffixing_manyUpTo (suffixing_seqRight hsep hp) n) fun _ =>
          suffixing_pure _)
      (suffixing_pure _)

/-! ## Inversion lemmas -/

/-- Inversion: a successful `manyUpTo` of a suffixing parser decomposes its
    input into the consumed tokens followed by the remainder, where each token
    is parsed by `p` from its own position (with everything after it as `rest`). -/
theorem manyUpTo_inv {p : Parser α} (hp : Suffixing p) :
    ∀ {n : ℕ} {l : List ℕ} {as : List α} {r : List ℕ},
      manyUpTo n p l = some (as, r) →
      ∃ toks : List (List ℕ), ∃ hlen : toks.length = as.length, as.length ≤ n ∧
        l = toks.flatten ++ r ∧
        ∀ i (hi : i < as.length),
          p (toks[i]'(by omega) ++ (toks.drop (i + 1)).flatten ++ r) =
            some (as[i], (toks.drop (i + 1)).flatten ++ r) := by
  intro n
  induction n with
  | zero =>
    intro l as r h
    simp only [manyUpTo_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, Nat.le_refl _, by simp, fun i hi => by simp at hi⟩
  | succ n ih =>
    intro l as r h
    rw [manyUpTo_succ] at h
    cases hpl : p l with
    | none =>
      simp only [hpl, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, by simp, by simp, fun i hi => by simp at hi⟩
    | some ar =>
      obtain ⟨a, r1⟩ := ar
      simp only [hpl, Option.map_eq_some_iff] at h
      obtain ⟨⟨as', r'⟩, hrec, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨toks, hlen, hle, hl, htok⟩ := ih hrec
      obtain ⟨t0, ht0⟩ := hp l a r1 hpl
      refine ⟨t0 :: toks, by simp [hlen], by simp; omega, ?_, ?_⟩
      · simp only [List.flatten_cons, List.append_assoc]
        rw [ht0, hl]
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero]
          rw [List.append_assoc, ← hl, ← ht0]
          exact hpl
        | succ i =>
          simp only [List.getElem_cons_succ, List.drop_succ_cons]
          exact htok i (by simpa using hi)

/-- Closed form of bounded repetition of `satisfy`: it takes the longest prefix
    of bytes satisfying `q`, cut at `n`. -/
theorem manyUpTo_satisfy (q : ℕ → Bool) :
    ∀ (n : ℕ) (l : List ℕ),
      manyUpTo n (satisfy q) l =
        some ((l.takeWhile q).take n, l.drop (min n (l.takeWhile q).length)) := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ n ih =>
    intro l
    cases l with
    | nil => exact manyUpTo_succ_of_none rfl n
    | cons c t =>
      by_cases hc : q c = true
      · have hs : satisfy q (c :: t) = some (c, t) := by simp [hc]
        have hmin : min (n + 1) ((List.takeWhile q t).length + 1)
            = min n (List.takeWhile q t).length + 1 := by omega
        rw [manyUpTo_succ_of_some hs, ih]
        simp [hc, hmin]
      · have hc' : q c = false := by simpa using hc
        have hs : satisfy q (c :: t) = none := by simp [hc']
        rw [manyUpTo_succ_of_none hs]
        simp [hc']

/-- Bounded repetition of a parser that returns each byte it consumes: on an
    input `k ++ rest` where `p` consumes exactly one byte from every position
    inside `k` and fails on `rest`, it consumes exactly `k`. -/
theorem manyUpTo_bytes {p : Parser ℕ} {k rest : List ℕ}
    (hk : ∀ c ∈ k, ∀ tl : List ℕ, p (c :: tl) = some (c, tl)) (hstop : p rest = none)
    {n : ℕ} (hn : k.length ≤ n) :
    manyUpTo n p (k ++ rest) = some (k, rest) := by
  induction k generalizing n with
  | nil =>
    cases n with
    | zero => simp
    | succ n => simpa using manyUpTo_succ_of_none hstop n
  | cons c k ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      have hc := hk c (List.mem_cons_self ..) (k ++ rest)
      rw [List.cons_append, manyUpTo_succ_of_some hc,
        ih (fun x hx => hk x (List.mem_cons_of_mem _ hx)) (by simpa using hn)]
      rfl

/-- Unbounded repetition of such a parser: the bound `many` picks is always
    large enough. -/
theorem many_bytes {p : Parser ℕ} {k rest : List ℕ}
    (hk : ∀ c ∈ k, ∀ tl : List ℕ, p (c :: tl) = some (c, tl)) (hstop : p rest = none) :
    many p (k ++ rest) = some (k, rest) := by
  rw [many_apply]
  exact manyUpTo_bytes hk hstop (by simp)

/-- A literal fails as soon as the first byte differs. -/
theorem literal_cons_of_ne {b c : ℕ} {bs r : List ℕ} (h : ¬ c = b) :
    literal (b :: bs) (c :: r) = none := by
  rw [literal_cons, byte_cons, if_neg h]
  rfl

end Parser

end Specs
