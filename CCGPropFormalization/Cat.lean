import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# CCG categories and the "replace head" relation

* `Cat Atom` — categories built from atoms with forward slash `X ⫽ Y` (X/Y)
  and backward slash `X ⧵ Y` (X\Y).
* `Slash`, `Cat.slash` — a uniform way to write `X | Y` for either slash.
* `ReplaceHead Y X A B` — `A = Y|Z₁|…|Zₙ` and `B = X|Z₁|…|Zₙ` (same
  slashes, same arguments, only the innermost *head* `Y` replaced by `X`).
  Generalized composition is defined on top of this relation, so that
  `B¹, B², …` are never enumerated separately.
-/

namespace CCG

/-- Slash direction: `fwd` is `/`, `bwd` is `\`. -/
inductive Slash
  | fwd
  | bwd
  deriving DecidableEq, Repr

/-- CCG categories over a type of atomic categories `Atom` (e.g. `S`, `NP`).
`fwd X Y` is `X/Y` (wants a `Y` to its right), `bwd X Y` is `X\Y` (wants a `Y` to its left). -/
inductive Cat (Atom : Type)
  | atom : Atom → Cat Atom
  | fwd : Cat Atom → Cat Atom → Cat Atom
  | bwd : Cat Atom → Cat Atom → Cat Atom
  deriving DecidableEq, Repr

/-- `X ⫽ Y` is the CCG category `X/Y`. Left associative: `X ⫽ Y ⫽ Z = (X/Y)/Z`. -/
infixl:70 " ⫽ " => Cat.fwd
/-- `X ⧵ Y` is the CCG category `X\Y`. Left associative: `X ⧵ Y ⧵ Z = (X\Y)\Z`. -/
infixl:70 " ⧵ " => Cat.bwd

variable {Atom : Type}

namespace Cat

/-- `X.slash s Y` is `X/Y` or `X\Y` depending on `s`; written `X | Y` in CCG papers. -/
def slash (X : Cat Atom) : Slash → Cat Atom → Cat Atom
  | .fwd, Y => X ⫽ Y
  | .bwd, Y => X ⧵ Y

@[simp] theorem slash_fwd (X Y : Cat Atom) : X.slash .fwd Y = X ⫽ Y := rfl
@[simp] theorem slash_bwd (X Y : Cat Atom) : X.slash .bwd Y = X ⧵ Y := rfl

/-- `X.slash s Y` is never atomic. -/
theorem slash_ne_atom (X : Cat Atom) (s : Slash) (Y : Cat Atom) (a : Atom) :
    X.slash s Y ≠ atom a := by
  cases s <;> simp [slash]

/-- Injectivity of `slash`: `X | Y = X' |' Y'` forces equal slashes, heads and arguments. -/
theorem slash_inj {X X' Y Y' : Cat Atom} {s s' : Slash} (h : X.slash s Y = X'.slash s' Y') :
    s = s' ∧ X = X' ∧ Y = Y' := by
  cases s <;> cases s' <;> simp_all [slash]

@[simp] theorem slash_eq_atom_iff (X : Cat Atom) (s : Slash) (Y : Cat Atom) (a : Atom) :
    X.slash s Y = atom a ↔ False := by
  cases s <;> simp [slash]

@[simp] theorem slash_eq_fwd_iff (X : Cat Atom) (s : Slash) (Y X' Y' : Cat Atom) :
    X.slash s Y = X' ⫽ Y' ↔ s = .fwd ∧ X = X' ∧ Y = Y' := by
  cases s <;> simp [slash]

@[simp] theorem slash_eq_bwd_iff (X : Cat Atom) (s : Slash) (Y X' Y' : Cat Atom) :
    X.slash s Y = X' ⧵ Y' ↔ s = .bwd ∧ X = X' ∧ Y = Y' := by
  cases s <;> simp [slash]

/-- Peel a *spine* `[(s₁,Z₁), …, (sₙ,Zₙ)]` onto a head: `X.spine sp = X|Zₙ|…|Z₁`
(the first element of the list is the *outermost* argument). -/
def spine (X : Cat Atom) : List (Slash × Cat Atom) → Cat Atom
  | [] => X
  | (s, Z) :: sp => (X.spine sp).slash s Z

@[simp] theorem spine_nil (X : Cat Atom) : X.spine [] = X := rfl
@[simp] theorem spine_cons (X : Cat Atom) (s : Slash) (Z : Cat Atom) (sp) :
    X.spine ((s, Z) :: sp) = (X.spine sp).slash s Z := rfl

end Cat

/-- `ReplaceHead Y X A B` : `A` has the form `Y|Z₁|⋯|Zₙ` and `B` is the *same* category with
the head `Y` replaced by `X`, i.e. `B = X|Z₁|⋯|Zₙ` (`n ≥ 0`, identical slashes and arguments).
This is the recursive structure underlying generalized composition `Bⁿ`. -/
inductive ReplaceHead (Y X : Cat Atom) : Cat Atom → Cat Atom → Prop
  /-- `n = 0`: the head is the whole category. -/
  | refl : ReplaceHead Y X Y X
  /-- Add one more argument `Z` (with slash `s`) on the outside of both sides. -/
  | step (s : Slash) (Z : Cat Atom) {A B : Cat Atom} :
      ReplaceHead Y X A B → ReplaceHead Y X (A.slash s Z) (B.slash s Z)

namespace ReplaceHead

/-- `ReplaceHead` is exactly "peeling the same spine onto `Y` and onto `X`". -/
theorem iff_spine {Y X A B : Cat Atom} :
    ReplaceHead Y X A B ↔ ∃ sp : List (Slash × Cat Atom), A = Y.spine sp ∧ B = X.spine sp := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl, rfl⟩
    | step s Z _ ih =>
      obtain ⟨sp, rfl, rfl⟩ := ih
      exact ⟨(s, Z) :: sp, rfl, rfl⟩
  · rintro ⟨sp, rfl, rfl⟩
    induction sp with
    | nil => exact refl
    | cons p _ ih => obtain ⟨s, Z⟩ := p; exact step s Z ih

/-- If the replaced result is atomic then no argument was peeled: `n = 0`. -/
theorem eq_of_atom {Y X A B : Cat Atom} {a : Atom} (h : ReplaceHead Y X A B)
    (hB : B = Cat.atom a) : A = Y ∧ X = Cat.atom a := by
  cases h with
  | refl => exact ⟨rfl, hB⟩
  | step s Z _ => exact absurd hB (Cat.slash_ne_atom _ s Z a)

/-- Inversion principle for `ReplaceHead` (avoids dependent elimination through `Cat.slash`). -/
theorem inv {Y X A B : Cat Atom} (h : ReplaceHead Y X A B) :
    (A = Y ∧ B = X) ∨ ∃ s Z A' B', ReplaceHead Y X A' B' ∧ A = A'.slash s Z ∧ B = B'.slash s Z := by
  cases h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | step s Z h => exact Or.inr ⟨s, Z, _, _, h, rfl, rfl⟩

/-- If the left-hand side is atomic then no argument was peeled: `n = 0`. -/
theorem atom_left {Y X A B : Cat Atom} {a : Atom} (h : ReplaceHead Y X A B)
    (hA : A = Cat.atom a) : Y = Cat.atom a ∧ B = X := by
  cases h with
  | refl => exact ⟨hA, rfl⟩
  | step s Z _ => exact absurd hA (Cat.slash_ne_atom _ s Z a)

end ReplaceHead

end CCG
