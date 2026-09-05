import CCGPropFormalization.Derivation

/-!
# The positive results (and why they are degenerate)

The target proposition

  `FA/BA + unrestricted TR + generalized composition ⇒ prefix reducibility`

is **true** — but for a trivial reason: with an *unrestricted* type-raising target `T`,
any two categories `A B` combine:

  `A ⇒ T/(T\A)`,  `B ⇒ (T\A)/((T\A)\B)`,  then `B¹` gives `T/((T\A)\B)`.

Hence *every* sequence of categories is prefix reducible, whether or not it has a full
derivation, and the hypothesis `∃ C, Derives lex 0 n C` of the target theorem is never used
(it is in fact always satisfied).  All of this is proved for the tiny fragment
`Rules.minimal` (forward TR + `B¹`) and transported to every larger rule set.
-/

namespace CCG

variable {Atom : Type} {n : ℕ}

/-- **Root cause of the degeneracy.**  Any two categories combine after one forward type raising
each, using plain `B¹` only.  The type-raising target is chosen to be `A` itself
(any category would do). -/
theorem Rules.minimal_combine_any (A B : Cat Atom) :
    ∃ A' B' C, Rules.minimal.unary A A' ∧ Rules.minimal.unary B B' ∧ Rules.minimal.bin A' B' C :=
  ⟨A ⫽ (A ⧵ A), (A ⧵ A) ⫽ ((A ⧵ A) ⧵ B), A ⫽ ((A ⧵ A) ⧵ B),
    ⟨A, rfl⟩, ⟨A ⧵ A, rfl⟩, ⟨A, A ⧵ A, (A ⧵ A) ⧵ B, rfl, rfl, rfl⟩⟩

/-- The same fact stated with the concrete rules `TypeRaise` / `Combine`. -/
theorem Combine.any (A B : Cat Atom) :
    ∃ A' B' C, TypeRaise A A' ∧ TypeRaise B B' ∧ Combine A' B' C :=
  ⟨_, _, _, TypeRaise.fwd A A, TypeRaise.fwd (A ⧵ A) B, Combine.fcomp₁ A (A ⧵ A) ((A ⧵ A) ⧵ B)⟩

/-- Every span `[i, j)` (with `i < j ≤ n`) has a *left-branching* derivation in the minimal
fragment, for **any** lexicon. -/
theorem LeftSpine.exists_minimal (lex : Fin n → Cat Atom) :
    ∀ j i, i < j → j ≤ n → ∃ C, LeftSpine Rules.minimal lex i j C
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | j + 1, i, hij, hjn => by
    rcases Nat.lt_or_ge i j with h | h
    · obtain ⟨C, hC⟩ := LeftSpine.exists_minimal lex j i h (by omega)
      obtain ⟨A', B', D, hA, hB, hD⟩ := Rules.minimal_combine_any C (lex ⟨j, hjn⟩)
      exact ⟨D, LeftSpine.bin (LeftSpine.unary hC hA)
        (LeftSpine.unary (LeftSpine.lex ⟨j, hjn⟩) hB) hD⟩
    · obtain rfl : i = j := by omega
      exact ⟨lex ⟨i, hjn⟩, LeftSpine.lex ⟨i, hjn⟩⟩

/-- Every span has a left-branching derivation in any rule set containing the minimal fragment. -/
theorem LeftSpine.exists_of_le {R : Rules Atom} (hR : Rules.minimal ≤ R) (lex : Fin n → Cat Atom)
    {i j : ℕ} (hij : i < j) (hjn : j ≤ n) : ∃ C, LeftSpine R lex i j C :=
  let ⟨C, hC⟩ := LeftSpine.exists_minimal lex j i hij hjn
  ⟨C, hC.mono hR⟩

/-- Every span reduces to *something*, in any rule set containing the minimal fragment. -/
theorem Derives.exists_of_le {R : Rules Atom} (hR : Rules.minimal ≤ R) (lex : Fin n → Cat Atom)
    {i j : ℕ} (hij : i < j) (hjn : j ≤ n) : ∃ C, Derives R lex i j C :=
  let ⟨C, hC⟩ := LeftSpine.exists_of_le hR lex hij hjn
  ⟨C, hC.toDerives⟩

/-- **Unconditional prefix reducibility.**  No full derivation is needed. -/
theorem prefixReducible_of_le {R : Rules Atom} (hR : Rules.minimal ≤ R) (lex : Fin n → Cat Atom) :
    PrefixReducible R lex :=
  fun _ hi hin => Derives.exists_of_le hR lex hi hin

/-- Unconditional prefix reducibility for the full system. -/
theorem prefixReducible_full (lex : Fin n → Cat Atom) : PrefixReducible Rules.full lex :=
  prefixReducible_of_le Rules.minimal_le_full lex

/-- **The target theorem, exactly as stated.**  It holds — but note that the proof discards `h`:
see `prefixReducible_full` and the README. -/
theorem prefix_reducible_of_full_derivation (lex : Fin n → Cat Atom)
    (h : ∃ C, Derives Rules.full lex 0 n C) : PrefixReducible Rules.full lex :=
  let _ := h
  prefixReducible_full lex

/-- The hypothesis of the target theorem is itself always satisfied (for non-empty sentences). -/
theorem exists_full_derivation (lex : Fin n → Cat Atom) (hn : 0 < n) :
    ∃ C, Derives Rules.full lex 0 n C :=
  Derives.exists_of_le Rules.minimal_le_full lex hn le_rfl

/-- **Weak normalization**: every full derivation can be replaced by a left-branching one —
with a possibly *different* final category.  (The version with the *same* category is false:
see `Audit/Strong.lean`.)  Again the hypothesis is not used. -/
theorem weak_left_spine_normalization (lex : Fin n → Cat Atom) {C : Cat Atom}
    (h : Derives Rules.full lex 0 n C) : ∃ C', LeftSpine Rules.full lex 0 n C' :=
  LeftSpine.exists_of_le Rules.minimal_le_full lex h.lt h.le_n

end CCG
