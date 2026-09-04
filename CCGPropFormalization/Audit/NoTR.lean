import CCGPropFormalization.Positive

/-!
# Audit 1 — type raising is the missing ingredient

Without type raising the proposition is **false**.  Minimal counterexample (`n = 3`):

  `w₁ = X/Y`,  `w₂ = W`,  `w₃ = Y\W`      (atoms with `W ≠ Y`)

The whole sentence derives `X` (`W  Y\W ⇒ Y` by BA, then `X/Y  Y ⇒ X` by FA), but the prefix
`w₁ w₂ = X/Y  W` matches no binary rule at all: FA needs `W = Y`, BA needs `W` to be a backward
functor, and both compositions need `W` to be a functor.
`n = 3` is minimal because for `n ≤ 2` every proper prefix is a single word.

With type raising the prefix *does* reduce, e.g. `W ⇒ Y/(Y\W)` and then
`X/Y  Y/(Y\W) ⇒ X/(Y\W)` by `B¹` — and note that the TR target `Y` is dictated by the
*continuation* `w₃`, not by the prefix itself.
-/

namespace CCG

open Cat

variable {Atom : Type}

/-- The lexicon `[X/Y, W, Y\W]`. -/
def lexNoTR (X Y W : Atom) : Fin 3 → Cat Atom :=
  ![atom X ⫽ atom Y, atom W, atom Y ⧵ atom W]

/-- The whole sentence `X/Y  W  Y\W` derives `X` without any type raising. -/
theorem lexNoTR_full (X Y W : Atom) : Derives Rules.noTR (lexNoTR X Y W) 0 3 (atom X) :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.lex 1) (Derives.lex 2) (Combine.ba (atom Y) (atom W)))
    (Combine.fa (atom X) (atom Y))

/-- In the TR-free system, a one-word span derives only its lexical category. -/
theorem Derives.noTR_single {n : ℕ} {lex : Fin n → Cat Atom} {i j : ℕ} {C : Cat Atom}
    (h : Derives Rules.noTR lex i j C) (hj : j = i + 1) (hi : i < n) : C = lex ⟨i, hi⟩ := by
  have := h.single hj hi
  clear h
  induction this with
  | refl => rfl
  | tail _ h => exact h.elim

/-- The prefix `X/Y  W` derives **nothing** without type raising. -/
theorem lexNoTR_prefix_irreducible (X Y W : Atom) (hWY : W ≠ Y) :
    ¬ ∃ C, Derives Rules.noTR (lexNoTR X Y W) 0 2 C := by
  rintro ⟨C, h⟩
  obtain ⟨A, B, C₀, hA, hB, hbin, -⟩ := h.two rfl (by omega) (by omega)
  have hA' : A = atom X ⫽ atom Y := by
    induction hA with
    | refl => rfl
    | tail _ h => exact h.elim
  have hB' : B = atom W := by
    induction hB with
    | refl => rfl
    | tail _ h => exact h.elim
  subst hA' hB'
  rcases hbin.inv with ⟨X', Y', h₁, h₂, -⟩ | ⟨X', Y', -, h₂, -⟩ |
      ⟨_, _, _, _, _, _, -, -, h₂, -⟩ | ⟨_, _, _, _, _, _, -, -, h₂, -⟩
  · cases h₁; cases h₂; exact hWY rfl
  · cases h₂
  · exact slash_ne_atom _ _ _ _ h₂.symm
  · cases h₂

/-- **Counterexample theorem.**  Without type raising, a full derivation does *not* imply prefix
reducibility. -/
theorem not_prefixReducible_noTR (X Y W : Atom) (hWY : W ≠ Y) :
    (∃ C, Derives Rules.noTR (lexNoTR X Y W) 0 3 C) ∧ ¬ PrefixReducible Rules.noTR (lexNoTR X Y W) :=
  ⟨⟨_, lexNoTR_full X Y W⟩, fun hpr => lexNoTR_prefix_irreducible X Y W hWY (hpr 2 (by omega) (by omega))⟩

/-- With (unrestricted) type raising the very same prefix reduces, using the target `Y`
dictated by the third word. -/
theorem lexNoTR_prefix_reducible_with_TR (X Y W : Atom) :
    Derives Rules.full (lexNoTR X Y W) 0 2 (atom X ⫽ (atom Y ⧵ atom W)) :=
  Derives.bin (Derives.lex 0)
    (Derives.tr (Derives.lex 1) (TypeRaise.fwd (atom Y) (atom W)))
    (Combine.fcomp₁ (atom X) (atom Y) (atom Y ⧵ atom W))

end CCG
