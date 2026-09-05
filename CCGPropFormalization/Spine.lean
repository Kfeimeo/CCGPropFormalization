import CCGPropFormalization.Cat

/-!
# Argument spines

`flattenSpine C` splits a category along its **result (head) spine only**:

* `((X\A)/B)/C ↦ (X, [(bwd, A), (fwd, B), (fwd, C)])` — slots listed innermost first;
* `X\(A/B) ↦ (X, [(bwd, A/B)])` — argument categories are **never** entered.

`rebuildSpine` is the inverse.  The head returned by `flattenSpine` is always an atom.
-/

namespace CCG

variable {Atom : Type}

/-- Direction of an argument slot (`/` or `\`); the same type as `Slash`. -/
abbrev Dir := Slash

/-- One slot of the outer argument spine: a direction together with an *opaque* argument category.
ASP moves whole slots; it never separates a direction from its argument. -/
structure ArgSlot (Atom : Type) where
  dir : Dir
  arg : Cat Atom
  deriving DecidableEq, Repr

/-- Flatten a category along its result spine (arguments stay opaque). -/
def flattenSpine : Cat Atom → Cat Atom × List (ArgSlot Atom)
  | .atom a => (.atom a, [])
  | .fwd X A => ((flattenSpine X).1, (flattenSpine X).2 ++ [⟨.fwd, A⟩])
  | .bwd X A => ((flattenSpine X).1, (flattenSpine X).2 ++ [⟨.bwd, A⟩])

/-- Rebuild a category from a head and a slot list: `rebuildSpine X [s₁, …, sₙ] = X |₁ A₁ ⋯ |ₙ Aₙ`. -/
def rebuildSpine (X : Cat Atom) : List (ArgSlot Atom) → Cat Atom
  | [] => X
  | s :: sl => rebuildSpine (X.slash s.dir s.arg) sl

/-- Number of outer argument slots (the *valency*). -/
def spineLength (C : Cat Atom) : ℕ := (flattenSpine C).2.length

@[simp] theorem flattenSpine_atom (a : Atom) : flattenSpine (Cat.atom a) = (Cat.atom a, []) := rfl
@[simp] theorem flattenSpine_fwd (X A : Cat Atom) :
    flattenSpine (X ⫽ A) = ((flattenSpine X).1, (flattenSpine X).2 ++ [⟨.fwd, A⟩]) := rfl
@[simp] theorem flattenSpine_bwd (X A : Cat Atom) :
    flattenSpine (X ⧵ A) = ((flattenSpine X).1, (flattenSpine X).2 ++ [⟨.bwd, A⟩]) := rfl
@[simp] theorem flattenSpine_slash (X : Cat Atom) (d : Dir) (A : Cat Atom) :
    flattenSpine (X.slash d A) = ((flattenSpine X).1, (flattenSpine X).2 ++ [⟨d, A⟩]) := by
  cases d <;> rfl

@[simp] theorem rebuildSpine_nil (X : Cat Atom) : rebuildSpine X [] = X := rfl
@[simp] theorem rebuildSpine_cons (X : Cat Atom) (s : ArgSlot Atom) (sl) :
    rebuildSpine X (s :: sl) = rebuildSpine (X.slash s.dir s.arg) sl := rfl

theorem rebuildSpine_append (X : Cat Atom) (l₁ l₂ : List (ArgSlot Atom)) :
    rebuildSpine X (l₁ ++ l₂) = rebuildSpine (rebuildSpine X l₁) l₂ := by
  induction l₁ generalizing X with
  | nil => rfl
  | cons s l ih => simp [ih]

@[simp] theorem rebuildSpine_concat (X : Cat Atom) (l : List (ArgSlot Atom)) (s : ArgSlot Atom) :
    rebuildSpine X (l ++ [s]) = (rebuildSpine X l).slash s.dir s.arg := by
  rw [rebuildSpine_append]; rfl

/-- **Round trip 1**: rebuilding the flattened spine gives the category back. -/
@[simp] theorem rebuild_flatten (C : Cat Atom) :
    rebuildSpine (flattenSpine C).1 (flattenSpine C).2 = C := by
  induction C with
  | atom a => rfl
  | fwd X A ih => simp [ih]
  | bwd X A ih => simp [ih]

/-- **Round trip 2** (normalization): flattening a rebuilt category appends the slots. -/
@[simp] theorem flatten_rebuild (X : Cat Atom) (sl : List (ArgSlot Atom)) :
    flattenSpine (rebuildSpine X sl) = ((flattenSpine X).1, (flattenSpine X).2 ++ sl) := by
  induction sl generalizing X with
  | nil => simp
  | cons s sl ih => simp [ih]

theorem flatten_rebuild_atom (a : Atom) (sl : List (ArgSlot Atom)) :
    flattenSpine (rebuildSpine (Cat.atom a) sl) = (Cat.atom a, sl) := by simp

/-- The head of a flattened spine is always atomic. -/
theorem flattenSpine_head_isAtom (C : Cat Atom) : ∃ a, (flattenSpine C).1 = Cat.atom a := by
  induction C with
  | atom a => exact ⟨a, rfl⟩
  | fwd X A ih => simpa using ih
  | bwd X A ih => simpa using ih

/-- `flattenSpine` is injective (it is a bijection onto `Atom × List (ArgSlot Atom)`). -/
theorem flattenSpine_injective {C C' : Cat Atom} (h : flattenSpine C = flattenSpine C') : C = C' := by
  rw [← rebuild_flatten C, ← rebuild_flatten C', h]

/-- Characterisation of `flattenSpine C = (X, sl)`. -/
theorem flattenSpine_eq_iff {C X : Cat Atom} {sl : List (ArgSlot Atom)} :
    flattenSpine C = (X, sl) ↔ (∃ a, X = Cat.atom a) ∧ C = rebuildSpine X sl := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := flattenSpine_head_isAtom C
    refine ⟨⟨a, ?_⟩, ?_⟩
    · rw [← ha, h]
    · rw [← rebuild_flatten C, h]
  · rintro ⟨⟨a, rfl⟩, rfl⟩
    simp

@[simp] theorem spineLength_atom (a : Atom) : spineLength (Cat.atom a) = 0 := rfl
@[simp] theorem spineLength_slash (X : Cat Atom) (d : Dir) (A : Cat Atom) :
    spineLength (X.slash d A) = spineLength X + 1 := by
  simp [spineLength]

/-! ### Relation to the outermost-first `Cat.spine` used by `ReplaceHead` -/

theorem Cat.spine_append (X : Cat Atom) (l₁ l₂ : List (Slash × Cat Atom)) :
    X.spine (l₁ ++ l₂) = (X.spine l₂).spine l₁ := by
  induction l₁ with
  | nil => rfl
  | cons p l ih => obtain ⟨s, Z⟩ := p; simp [ih]

/-- `ArgSlot` as a `(Slash, Cat)` pair. -/
def ArgSlot.toPair (s : ArgSlot Atom) : Slash × Cat Atom := (s.dir, s.arg)
/-- A `(Slash, Cat)` pair as an `ArgSlot`. -/
def ArgSlot.ofPair (p : Slash × Cat Atom) : ArgSlot Atom := ⟨p.1, p.2⟩

@[simp] theorem ArgSlot.toPair_ofPair (p : Slash × Cat Atom) : (ArgSlot.ofPair p).toPair = p := rfl
@[simp] theorem ArgSlot.ofPair_toPair (s : ArgSlot Atom) : ArgSlot.ofPair s.toPair = s := rfl

/-- `rebuildSpine` (innermost first) is `Cat.spine` (outermost first) on the reversed list. -/
theorem rebuildSpine_eq_spine (X : Cat Atom) (sl : List (ArgSlot Atom)) :
    rebuildSpine X sl = X.spine (sl.map ArgSlot.toPair).reverse := by
  induction sl generalizing X with
  | nil => rfl
  | cons s sl ih =>
    simp only [rebuildSpine_cons, ih, List.map_cons, List.reverse_cons, Cat.spine_append]
    rfl

/-- `ReplaceHead` in terms of `rebuildSpine`: generalized composition replaces the head of a
spine and keeps every slot. -/
theorem ReplaceHead.iff_rebuild {Y X A B : Cat Atom} :
    ReplaceHead Y X A B ↔ ∃ sl : List (ArgSlot Atom), A = rebuildSpine Y sl ∧ B = rebuildSpine X sl := by
  rw [ReplaceHead.iff_spine]
  constructor
  · rintro ⟨sp, rfl, rfl⟩
    refine ⟨(sp.map ArgSlot.ofPair).reverse, ?_, ?_⟩ <;>
      simp [rebuildSpine_eq_spine, List.map_reverse, Function.comp_def]
  · rintro ⟨sl, rfl, rfl⟩
    exact ⟨(sl.map ArgSlot.toPair).reverse, rebuildSpine_eq_spine _ _, rebuildSpine_eq_spine _ _⟩

end CCG
