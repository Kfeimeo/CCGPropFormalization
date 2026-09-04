import CCGPropFormalization.Cat

/-!
# CCG combinatory rules

* `TypeRaise A B` — *unrestricted* type raising: `A ⇒ T/(T\A)` and `A ⇒ T\(T/A)` for **any** `T`.
* `Combine A B C` — the binary rules: forward/backward application (FA/BA) and
  generalized forward/backward composition, defined via `ReplaceHead`.
* `Rules` — a package (unary rules, binary rules) so that the *same* `Derives`
  relation can be instantiated with the full system, with the TR-free system, or with the tiny
  "forward TR + B¹" fragment.  This is what makes the theorem audit precise: every
  positive result is proved for the *smallest* rule set that supports it and transported upwards by
  monotonicity, and every counterexample is proved for the *largest* rule set and transported
  downwards.
-/

namespace CCG

variable {Atom : Type}

/-- Unrestricted type raising.  `fwd T A : A ⇒ T/(T\A)`,  `bwd T A : A ⇒ T\(T/A)`.
The target `T` is completely free — this is what "unrestricted" means. -/
inductive TypeRaise : Cat Atom → Cat Atom → Prop
  | fwd (T A : Cat Atom) : TypeRaise A (T ⫽ (T ⧵ A))
  | bwd (T A : Cat Atom) : TypeRaise A (T ⧵ (T ⫽ A))

/-- Binary combination `Combine A B C` : "`A B ⇒ C`". -/
inductive Combine : Cat Atom → Cat Atom → Cat Atom → Prop
  /-- FA: `X/Y  Y ⇒ X`. -/
  | fa (X Y : Cat Atom) : Combine (X ⫽ Y) Y X
  /-- BA: `Y  X\Y ⇒ X`. -/
  | ba (X Y : Cat Atom) : Combine Y (X ⧵ Y) X
  /-- Generalized forward composition `Bⁿ` (`n ≥ 1`, any slashes in the spine, so this
  includes the crossed instances): `X/Y   Y|Z₁|⋯|Zₙ ⇒ X|Z₁|⋯|Zₙ`.
  `ReplaceHead Y X A B` handles `Y|Z₁|⋯|Zₙ₋₁ ↦ X|Z₁|⋯|Zₙ₋₁`; the last `|Zₙ` is `slash s Z`. -/
  | fcomp {X Y A B : Cat Atom} (s : Slash) (Z : Cat Atom) :
      ReplaceHead Y X A B → Combine (X ⫽ Y) (A.slash s Z) (B.slash s Z)
  /-- Generalized backward composition (`n ≥ 1`, any slashes): `Y|Z₁|⋯|Zₙ   X\Y ⇒ X|Z₁|⋯|Zₙ`.
  Not needed for any positive result below; it is included so that the *negative* results
  (counterexamples) are robust against adding it.  See the README. -/
  | bcomp {X Y A B : Cat Atom} (s : Slash) (Z : Cat Atom) :
      ReplaceHead Y X A B → Combine (A.slash s Z) (X ⧵ Y) (B.slash s Z)

/-- Inversion principle for `Combine` (avoids dependent elimination through `Cat.slash`). -/
theorem Combine.inv {A B C : Cat Atom} (h : Combine A B C) :
    (∃ X Y, A = X ⫽ Y ∧ B = Y ∧ C = X) ∨
    (∃ X Y, A = Y ∧ B = X ⧵ Y ∧ C = X) ∨
    (∃ X Y A' B' s Z, ReplaceHead Y X A' B' ∧ A = X ⫽ Y ∧ B = A'.slash s Z ∧ C = B'.slash s Z) ∨
    (∃ X Y A' B' s Z, ReplaceHead Y X A' B' ∧ A = A'.slash s Z ∧ B = X ⧵ Y ∧ C = B'.slash s Z) := by
  cases h with
  | fa => exact Or.inl ⟨_, _, rfl, rfl, rfl⟩
  | ba => exact Or.inr (Or.inl ⟨_, _, rfl, rfl, rfl⟩)
  | fcomp _ _ hr => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, hr, rfl, rfl, rfl⟩))
  | bcomp _ _ hr => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, hr, rfl, rfl, rfl⟩))

/-- Type raising never produces an atomic category. -/
theorem TypeRaise.ne_atom {A B : Cat Atom} (h : TypeRaise A B) (a : Atom) : B ≠ Cat.atom a := by
  cases h <;> simp

/-- Plain forward composition `B¹`: `X/Y  Y/Z ⇒ X/Z` is an instance of `Combine.fcomp`. -/
theorem Combine.fcomp₁ (X Y Z : Cat Atom) : Combine (X ⫽ Y) (Y ⫽ Z) (X ⫽ Z) :=
  Combine.fcomp .fwd Z ReplaceHead.refl

/-- A rule set: a unary relation (type raising) and a binary relation (combination). -/
structure Rules (Atom : Type) where
  /-- Unary rules applied to a single constituent (type raising). -/
  tr : Cat Atom → Cat Atom → Prop
  /-- Binary rules combining two adjacent constituents. -/
  bin : Cat Atom → Cat Atom → Cat Atom → Prop

namespace Rules

/-- `R₁ ≤ R₂` : every rule of `R₁` is a rule of `R₂`. -/
instance : LE (Rules Atom) :=
  ⟨fun R₁ R₂ => (∀ A B, R₁.tr A B → R₂.tr A B) ∧ (∀ A B C, R₁.bin A B C → R₂.bin A B C)⟩

theorem le_def {R₁ R₂ : Rules Atom} :
    R₁ ≤ R₂ ↔ (∀ A B, R₁.tr A B → R₂.tr A B) ∧ (∀ A B C, R₁.bin A B C → R₂.bin A B C) :=
  Iff.rfl

/-- The full system: FA + BA + generalized (forward & backward) composition + unrestricted TR. -/
def full : Rules Atom := ⟨TypeRaise, Combine⟩

/-- The same binary rules but **no** type raising. -/
def noTR : Rules Atom := ⟨fun _ _ => False, Combine⟩

/-- The tiny fragment `forward TR (any target) + B¹`.  It already makes every sequence of
categories reducible, which is the root cause of the degeneracy exposed by the audit. -/
def minimal : Rules Atom :=
  ⟨fun A B => ∃ T, B = T ⫽ (T ⧵ A),
   fun A B C => ∃ X Y Z, A = X ⫽ Y ∧ B = Y ⫽ Z ∧ C = X ⫽ Z⟩

theorem minimal_le_full : (minimal : Rules Atom) ≤ full := by
  refine ⟨?_, ?_⟩
  · rintro A B ⟨T, rfl⟩; exact TypeRaise.fwd T A
  · rintro A B C ⟨X, Y, Z, rfl, rfl, rfl⟩; exact Combine.fcomp₁ X Y Z

theorem noTR_le_full : (noTR : Rules Atom) ≤ full :=
  ⟨fun _ _ h => h.elim, fun _ _ _ h => h⟩

end Rules

end CCG
