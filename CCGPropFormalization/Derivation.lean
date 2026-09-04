import CCGPropFormalization.Rules

/-!
# Span derivations, left-spine derivations, prefix reducibility

Given lexical categories `lex : Fin n → Cat Atom`, `Derives R lex i j C` means the span
`[i, j)` of words can be reduced to `C` using the rule set `R`.

* `Derives` — arbitrary (binary-branching) derivations: lexical item / type raising / binary rule.
* `LeftSpine` — left-branching derivations `(((w₁ w₂) w₃) ⋯ wₙ)`, i.e. the incremental,
  left-to-right ones (type raising allowed at every node).
* `PrefixReducible R lex` — every non-empty prefix `[0, i)` reduces to *some* category.
-/

namespace CCG

variable {Atom : Type} {n : ℕ}

/-- `Derives R lex i j C` : the span `[i, j)` reduces to `C`. -/
inductive Derives (R : Rules Atom) (lex : Fin n → Cat Atom) : ℕ → ℕ → Cat Atom → Prop
  /-- A single word is its lexical category. -/
  | lex (i : Fin n) : Derives R lex i (i + 1) (lex i)
  /-- A unary rule (type raising) applied to any constituent. -/
  | tr {i j : ℕ} {C D : Cat Atom} : Derives R lex i j C → R.tr C D → Derives R lex i j D
  /-- Two adjacent constituents combined by a binary rule. -/
  | bin {i k j : ℕ} {A B C : Cat Atom} :
      Derives R lex i k A → Derives R lex k j B → R.bin A B C → Derives R lex i j C

/-- Left-branching ("left spine") derivations: the right daughter of every binary node is a
single word (possibly type raised).  `LeftSpine R lex i j C` ⊆ `Derives R lex i j C`. -/
inductive LeftSpine (R : Rules Atom) (lex : Fin n → Cat Atom) : ℕ → ℕ → Cat Atom → Prop
  | lex (i : Fin n) : LeftSpine R lex i (i + 1) (lex i)
  | tr {i j : ℕ} {C D : Cat Atom} : LeftSpine R lex i j C → R.tr C D → LeftSpine R lex i j D
  | bin {i j : ℕ} {A B C : Cat Atom} :
      LeftSpine R lex i j A → LeftSpine R lex j (j + 1) B → R.bin A B C →
      LeftSpine R lex i (j + 1) C

/-- Prefix reducibility: every non-empty prefix `[0, i)` (`0 < i ≤ n`) reduces to some category. -/
def PrefixReducible (R : Rules Atom) (lex : Fin n → Cat Atom) : Prop :=
  ∀ i, 0 < i → i ≤ n → ∃ C, Derives R lex 0 i C

namespace Derives

variable {R : Rules Atom} {lex : Fin n → Cat Atom}

/-- Spans are non-empty and lie inside the sentence. -/
theorem lt_and_le {i j : ℕ} {C : Cat Atom} (h : Derives R lex i j C) : i < j ∧ j ≤ n := by
  induction h with
  | lex i => exact ⟨Nat.lt_succ_self _, i.isLt⟩
  | tr _ _ ih => exact ih
  | bin _ _ _ ih₁ ih₂ => exact ⟨lt_trans ih₁.1 ih₂.1, ih₂.2⟩

theorem lt {i j : ℕ} {C : Cat Atom} (h : Derives R lex i j C) : i < j := h.lt_and_le.1

theorem le_n {i j : ℕ} {C : Cat Atom} (h : Derives R lex i j C) : j ≤ n := h.lt_and_le.2

/-- Monotonicity in the rule set. -/
theorem mono {R' : Rules Atom} (hR : R ≤ R') {i j : ℕ} {C : Cat Atom}
    (h : Derives R lex i j C) : Derives R' lex i j C := by
  induction h with
  | lex i => exact Derives.lex i
  | tr _ hCD ih => exact tr ih (hR.1 _ _ hCD)
  | bin _ _ hABC ih₁ ih₂ => exact bin ih₁ ih₂ (hR.2 _ _ _ hABC)

/-- Derivations only look at the words inside the span. -/
theorem congr {lex' : Fin n → Cat Atom} {i j : ℕ} {C : Cat Atom}
    (h : Derives R lex i j C) (hl : ∀ k : Fin n, i ≤ k → k < j → lex k = lex' k) :
    Derives R lex' i j C := by
  induction h with
  | lex i => rw [hl i le_rfl (Nat.lt_succ_self _)]; exact Derives.lex i
  | tr _ hCD ih => exact tr (ih hl) hCD
  | bin h₁ h₂ hABC ih₁ ih₂ =>
    exact bin (ih₁ fun k h₁ h₂ => hl k h₁ (lt_trans h₂ (Derives.lt ‹_›)))
      (ih₂ fun k h₁' h₂' => hl k (le_trans (le_of_lt (Derives.lt ‹_›)) h₁') h₂') hABC

/-- A one-word span `[i, i+1)` derives exactly the `R.tr`-closure of the lexical category. -/
theorem single {i j : ℕ} {C : Cat Atom} (h : Derives R lex i j C) (hj : j = i + 1) (hi : i < n) :
    Relation.ReflTransGen R.tr (lex ⟨i, hi⟩) C := by
  induction h with
  | lex i₀ =>
    have : (⟨i₀, hi⟩ : Fin n) = i₀ := Fin.ext rfl
    rw [this]
  | tr _ hCD ih => exact (ih hj hi).tail hCD
  | bin h₁ h₂ _ _ _ =>
    have := h₁.lt; have := h₂.lt; omega

/-- A two-word span `[i, i+2)` is: type raise each word, combine once, type raise the result. -/
theorem two {i j : ℕ} {C : Cat Atom} (h : Derives R lex i j C) (hj : j = i + 2)
    (hi : i < n) (hi' : i + 1 < n) :
    ∃ A B C₀, Relation.ReflTransGen R.tr (lex ⟨i, hi⟩) A ∧
      Relation.ReflTransGen R.tr (lex ⟨i + 1, hi'⟩) B ∧ R.bin A B C₀ ∧
      Relation.ReflTransGen R.tr C₀ C := by
  induction h with
  | lex i₀ => omega
  | tr _ hCD ih =>
    obtain ⟨A, B, C₀, hA, hB, hbin, hC⟩ := ih hj hi hi'
    exact ⟨A, B, C₀, hA, hB, hbin, hC.tail hCD⟩
  | @bin i k j A B C h₁ h₂ hABC _ _ =>
    have hk : k = i + 1 := by have := h₁.lt; have := h₂.lt; omega
    subst hk
    exact ⟨A, B, C, h₁.single rfl hi, h₂.single (by omega) hi', hABC, Relation.ReflTransGen.refl⟩

end Derives

namespace LeftSpine

variable {R : Rules Atom} {lex : Fin n → Cat Atom}

/-- Every left-spine derivation is a derivation. -/
theorem toDerives {i j : ℕ} {C : Cat Atom} (h : LeftSpine R lex i j C) : Derives R lex i j C := by
  induction h with
  | lex i => exact Derives.lex i
  | tr _ hCD ih => exact Derives.tr ih hCD
  | bin _ _ hABC ih₁ ih₂ => exact Derives.bin ih₁ ih₂ hABC

theorem lt {i j : ℕ} {C : Cat Atom} (h : LeftSpine R lex i j C) : i < j := h.toDerives.lt

/-- Monotonicity in the rule set. -/
theorem mono {R' : Rules Atom} (hR : R ≤ R') {i j : ℕ} {C : Cat Atom}
    (h : LeftSpine R lex i j C) : LeftSpine R' lex i j C := by
  induction h with
  | lex i => exact LeftSpine.lex i
  | tr _ hCD ih => exact tr ih (hR.1 _ _ hCD)
  | bin _ _ hABC ih₁ ih₂ => exact bin ih₁ ih₂ (hR.2 _ _ _ hABC)

/-- Inversion for left-spine derivations: a span is either a single (type-raised) word, or the
result of combining a left-spine derivation of `[i, k)` with the word `k`, followed by type
raising. -/
theorem inv {i j : ℕ} {C : Cat Atom} (h : LeftSpine R lex i j C) :
    (∃ hi : i < n, j = i + 1 ∧ Relation.ReflTransGen R.tr (lex ⟨i, hi⟩) C) ∨
    (∃ k A B C₀, j = k + 1 ∧ LeftSpine R lex i k A ∧ LeftSpine R lex k (k + 1) B ∧
      R.bin A B C₀ ∧ Relation.ReflTransGen R.tr C₀ C) := by
  induction h with
  | lex i => exact Or.inl ⟨i.isLt, rfl, Relation.ReflTransGen.refl⟩
  | tr _ hCD ih =>
    rcases ih with ⟨hi, hj, hC⟩ | ⟨k, A, B, C₀, hj, h₁, h₂, hbin, hC⟩
    · exact Or.inl ⟨hi, hj, hC.tail hCD⟩
    · exact Or.inr ⟨k, A, B, C₀, hj, h₁, h₂, hbin, hC.tail hCD⟩
  | bin h₁ h₂ hbin => exact Or.inr ⟨_, _, _, _, rfl, h₁, h₂, hbin, Relation.ReflTransGen.refl⟩

end LeftSpine

/-- *Strong* (derivation-compatible) prefix reducibility with respect to a final category `C`:
every proper prefix reduces to a category that combines **in one step** with some reduction of
the remaining suffix to give `C`.  This is what one would need for the prefix categories to be
usable in an incremental parse to `C`.  It is **false** in general: see `Audit/Strong.lean`. -/
def StrongPrefixReducible (R : Rules Atom) (lex : Fin n → Cat Atom) (C : Cat Atom) : Prop :=
  ∀ i, 0 < i → i < n → ∃ P D, Derives R lex 0 i P ∧ Derives R lex i n D ∧ R.bin P D C

end CCG
