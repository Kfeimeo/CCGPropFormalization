import CCGPropFormalization.Derivation

/-!
# Continuations and grammatical acceptability

`Continues R lex i P j C` : a constituent `P` spanning `[0, i)` can be extended, using only the
words in `[i, j)`, to a constituent `C` spanning `[0, j)`.  Since every constituent starting at
`0` lies on the left spine of the tree, this is exactly "`P` over `[0, i)` is a constituent of
some derivation of `C` over `[0, j)`".

`GrammAcceptable R lex C` : every proper prefix has a category that the real suffix can
discharge to the final category `C`.  This is the "residual continuation must match the actual
suffix" requirement, strictly between `PrefixReducible` (any category) and
`StrongPrefixReducible` (one-step discharge).
-/

namespace CCG

variable {Atom : Type} {n : ℕ}

/-- `Continues R lex i P j C` : `P` over `[0, i)` extends to `C` over `[0, j)` via the words
in `[i, j)`. -/
inductive Continues (R : Rules Atom) (lex : Fin n → Cat Atom) (i : ℕ) (P : Cat Atom) :
    ℕ → Cat Atom → Prop
  | refl : Continues R lex i P i P
  | unary {j : ℕ} {C D : Cat Atom} : Continues R lex i P j C → R.unary C D → Continues R lex i P j D
  | bin {j k : ℕ} {A B C : Cat Atom} :
      Continues R lex i P j A → Derives R lex j k B → R.bin A B C → Continues R lex i P k C

/-- Every proper prefix has a category that the actual suffix discharges to `C`. -/
def GrammAcceptable (R : Rules Atom) (lex : Fin n → Cat Atom) (C : Cat Atom) : Prop :=
  ∀ i, 0 < i → i < n → ∃ P, Derives R lex 0 i P ∧ Continues R lex i P n C

namespace Continues

variable {R : Rules Atom} {lex : Fin n → Cat Atom}

theorem le {i j : ℕ} {P C : Cat Atom} (h : Continues R lex i P j C) : i ≤ j := by
  induction h with
  | refl => exact le_rfl
  | unary _ _ ih => exact ih
  | bin _ hB _ ih => exact le_trans ih (le_of_lt hB.lt)

/-- A continuation of a derived prefix is a derivation of the whole. -/
theorem toDerives {i j : ℕ} {P C : Cat Atom} (hP : Derives R lex 0 i P)
    (h : Continues R lex i P j C) : Derives R lex 0 j C := by
  induction h with
  | refl => exact hP
  | unary _ hCD ih => exact ih.unary hCD
  | bin _ hB hABC ih => exact ih.bin hB hABC

theorem mono {R' : Rules Atom} (hR : R ≤ R') {i j : ℕ} {P C : Cat Atom}
    (h : Continues R lex i P j C) : Continues R' lex i P j C := by
  induction h with
  | refl => exact refl
  | unary _ hCD ih => exact unary ih (hR.1 _ _ hCD)
  | bin _ hB hABC ih => exact bin ih (hB.mono hR) (hR.2 _ _ _ hABC)

end Continues

/-- The first word is always a constituent of any derivation: prefix `1` is always acceptable. -/
theorem Derives.continues_first {R : Rules Atom} {lex : Fin n → Cat Atom} {j : ℕ} {C : Cat Atom}
    (h : Derives R lex 0 j C) (hn : 0 < n) : Continues R lex 1 (lex ⟨0, hn⟩) j C := by
  suffices H : ∀ i j C, Derives R lex i j C → i = 0 → Continues R lex 1 (lex ⟨0, hn⟩) j C from
    H 0 j C h rfl
  intro i j C h
  induction h with
  | lex i₀ =>
    intro hi
    have : i₀ = ⟨0, hn⟩ := Fin.ext hi
    subst this
    exact Continues.refl
  | unary _ hCD ih => intro hi; exact (ih hi).unary hCD
  | bin _ hB hABC ih _ => intro hi; exact (ih hi).bin hB hABC

/-- One-step discharge (`StrongPrefixReducible`) implies acceptability. -/
theorem GrammAcceptable.of_strong {R : Rules Atom} {lex : Fin n → Cat Atom} {C : Cat Atom}
    (h : StrongPrefixReducible R lex C) : GrammAcceptable R lex C := by
  intro i hi hin
  obtain ⟨P, D, hP, hD, hPD⟩ := h i hi hin
  exact ⟨P, hP, Continues.refl.bin hD hPD⟩

/-- Acceptability implies plain prefix reducibility (given the full derivation). -/
theorem GrammAcceptable.prefixReducible {R : Rules Atom} {lex : Fin n → Cat Atom} {C : Cat Atom}
    (hC : Derives R lex 0 n C) (h : GrammAcceptable R lex C) : PrefixReducible R lex := by
  intro i hi hin
  rcases Nat.lt_or_eq_of_le hin with hlt | rfl
  · obtain ⟨P, hP, -⟩ := h i hi hlt
    exact ⟨P, hP⟩
  · exact ⟨C, hC⟩

end CCG
