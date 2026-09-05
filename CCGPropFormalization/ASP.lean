import CCGPropFormalization.Spine
import CCGPropFormalization.Rules
import Mathlib.Data.Multiset.Defs

/-!
# Argument-Spine Permutation (ASP)

`ASP C C'` : `C` and `C'` have the same head and the argument slots of `C'` are a permutation of
the argument slots of `C`.  Slots `(direction, argument)` move as a whole; argument categories are
opaque.

Contents:
* `ASP` and its equivalence-relation properties, invariants (head, slot multiset, valency);
* the adjacent-swap presentation `AdjacentSwap` / `ASPStep` and the proof that `ASP` is exactly
  the reflexive–transitive closure of one local swap;
* rigidity lemmas (`ASP` cannot touch a category with ≤ 1 slot, cannot enter an argument,
  cannot swap a direction without its argument);
* the rule sets `Rules.app`, `Rules.appAsp`, `Rules.appCompAsp` (TR switched off) and the
  generic switch `Rules.withASP`.
-/

namespace CCG

variable {Atom : Type}

/-- **Argument-Spine Permutation.**  Same head, permuted slots. -/
def ASP (C C' : Cat Atom) : Prop :=
  (flattenSpine C).1 = (flattenSpine C').1 ∧ List.Perm (flattenSpine C).2 (flattenSpine C').2

instance [DecidableEq Atom] : DecidableRel (ASP (Atom := Atom)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

namespace ASP

/-- The definition in the form of the specification. -/
theorem iff_exists {C C' : Cat Atom} :
    ASP C C' ↔ ∃ X args args', flattenSpine C = (X, args) ∧ flattenSpine C' = (X, args') ∧
      List.Perm args args' := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨_, _, _, rfl, by rw [h₁], h₂⟩
  · rintro ⟨X, args, args', h₁, h₂, hp⟩
    exact ⟨by rw [h₁, h₂], by rw [h₁, h₂]; exact hp⟩

@[refl] theorem refl (C : Cat Atom) : ASP C C := ⟨rfl, List.Perm.refl _⟩
@[symm] theorem symm {C C' : Cat Atom} (h : ASP C C') : ASP C' C := ⟨h.1.symm, h.2.symm⟩
@[trans] theorem trans {C C' C'' : Cat Atom} (h : ASP C C') (h' : ASP C' C'') : ASP C C'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem equivalence : Equivalence (ASP (Atom := Atom)) := ⟨refl, symm, trans⟩

/-- `ASP` is already reflexive and transitive, so its closure adds nothing. -/
theorem rtg_iff {C C' : Cat Atom} : Relation.ReflTransGen ASP C C' ↔ ASP C C' := by
  constructor
  · intro h
    induction h with
    | refl => exact refl _
    | tail _ h ih => exact ih.trans h
  · exact Relation.ReflTransGen.single

/-! ### Invariants -/

/-- The head is unchanged. -/
theorem head_eq {C C' : Cat Atom} (h : ASP C C') : (flattenSpine C).1 = (flattenSpine C').1 := h.1
/-- The slot list is permuted. -/
theorem perm {C C' : Cat Atom} (h : ASP C C') : List.Perm (flattenSpine C).2 (flattenSpine C').2 := h.2
/-- The multiset of slots is unchanged. -/
theorem multiset_eq {C C' : Cat Atom} (h : ASP C C') :
    ((flattenSpine C).2 : Multiset (ArgSlot Atom)) = (flattenSpine C').2 :=
  Multiset.coe_eq_coe.mpr h.2
/-- The valency (spine length) is unchanged. -/
theorem spineLength_eq {C C' : Cat Atom} (h : ASP C C') : spineLength C = spineLength C' :=
  h.2.length_eq
/-- Every slot of `C'` — direction **and** argument category, unchanged — is a slot of `C`. -/
theorem slot_mem {C C' : Cat Atom} (h : ASP C C') {s : ArgSlot Atom} (hs : s ∈ (flattenSpine C').2) :
    s ∈ (flattenSpine C).2 :=
  h.2.mem_iff.mpr hs

/-! ### Rigidity: what ASP can *not* do -/

/-- A category with at most one slot is fixed by ASP. -/
theorem eq_of_spineLength_le_one {C C' : Cat Atom} (h : ASP C C') (hl : spineLength C ≤ 1) :
    C' = C := by
  apply flattenSpine_injective
  obtain ⟨h₁, h₂⟩ := h
  unfold spineLength at hl
  refine Prod.ext h₁.symm ?_
  match hC : (flattenSpine C).2, hl with
  | [], _ => rw [hC] at h₂; exact List.perm_nil.mp h₂.symm
  | [s], _ => rw [hC] at h₂; exact List.perm_singleton.mp h₂.symm

/-- Atoms are fixed by ASP. -/
theorem eq_of_atom {a : Atom} {C' : Cat Atom} (h : ASP (Cat.atom a) C') : C' = Cat.atom a :=
  h.eq_of_spineLength_le_one (by simp)

/-- One-slot functors are fixed by ASP — in particular the argument is never entered:
`X\(A/B)` stays `X\(A/B)`. -/
theorem eq_of_atom_slash {a : Atom} {d : Dir} {A C' : Cat Atom}
    (h : ASP ((Cat.atom a).slash d A) C') : C' = (Cat.atom a).slash d A :=
  h.eq_of_spineLength_le_one (by simp)

theorem eq_of_atom_fwd {a : Atom} {A C' : Cat Atom} (h : ASP (Cat.atom a ⫽ A) C') :
    C' = Cat.atom a ⫽ A :=
  h.eq_of_spineLength_le_one (by simp [spineLength])

theorem eq_of_atom_bwd {a : Atom} {A C' : Cat Atom} (h : ASP (Cat.atom a ⧵ A) C') :
    C' = Cat.atom a ⧵ A :=
  h.eq_of_spineLength_le_one (by simp [spineLength])

/-- ASP never modifies the inside of an argument: every argument category occurring in `C'`
occurs, with the same direction, in `C`. -/
theorem arg_mem {C C' : Cat Atom} (h : ASP C C') {d : Dir} {A : Cat Atom}
    (hs : (⟨d, A⟩ : ArgSlot Atom) ∈ (flattenSpine C').2) : (⟨d, A⟩ : ArgSlot Atom) ∈ (flattenSpine C).2 :=
  h.slot_mem hs

/-- Swapping the directions of two slots *without* their arguments is not an ASP step unless
the arguments coincide: `(X\A)/B ⇏ (X/A)\B` for `A ≠ B`. -/
theorem not_dir_swap {X A B : Cat Atom} (hAB : A ≠ B) : ¬ ASP ((X ⧵ A) ⫽ B) ((X ⫽ A) ⧵ B) := by
  rintro ⟨-, h⟩
  simp only [flattenSpine_fwd, flattenSpine_bwd, List.append_assoc, List.singleton_append,
    List.perm_append_left_iff] at h
  have := h.mem_iff.mp (List.mem_cons_self ..)
  simp [hAB] at this

/-! ### Congruence and the basic swap -/

/-- ASP is a congruence for adding an outer slot. -/
theorem slash_congr {C C' : Cat Atom} (h : ASP C C') (d : Dir) (Z : Cat Atom) :
    ASP (C.slash d Z) (C'.slash d Z) := by
  refine ⟨by simp [h.1], ?_⟩
  simp only [flattenSpine_slash]
  exact h.2.append_right _

/-- The basic ASP step: the two outermost slots may be exchanged. -/
theorem swap_outer (X : Cat Atom) (d₁ : Dir) (A : Cat Atom) (d₂ : Dir) (B : Cat Atom) :
    ASP ((X.slash d₁ A).slash d₂ B) ((X.slash d₂ B).slash d₁ A) := by
  refine ⟨by simp, ?_⟩
  simp only [flattenSpine_slash, List.append_assoc, List.singleton_append]
  exact List.Perm.append_left _ (List.Perm.swap _ _ _)

/-- `(X\A)/B ⇔ (X/B)\A`. -/
theorem bwd_fwd (X A B : Cat Atom) : ASP ((X ⧵ A) ⫽ B) ((X ⫽ B) ⧵ A) := swap_outer X .bwd A .fwd B
/-- `((X\A)/B)/C ⇔ ((X/B)\A)/C`. -/
theorem bwd_fwd_fwd (X A B C : Cat Atom) :
    ASP (((X ⧵ A) ⫽ B) ⫽ C) (((X ⫽ B) ⧵ A) ⫽ C) := (bwd_fwd X A B).slash_congr .fwd C
/-- `(X/A)/B ⇔ (X/B)/A`. -/
theorem fwd_fwd (X A B : Cat Atom) : ASP ((X ⫽ A) ⫽ B) ((X ⫽ B) ⫽ A) := swap_outer X .fwd A .fwd B
/-- `(X\A)\B ⇔ (X\B)\A`. -/
theorem bwd_bwd (X A B : Cat Atom) : ASP ((X ⧵ A) ⧵ B) ((X ⧵ B) ⧵ A) := swap_outer X .bwd A .bwd B

end ASP

/-! ### Adjacent-swap presentation -/

/-- One adjacent transposition somewhere in a list. -/
inductive AdjacentSwap {α : Type} : List α → List α → Prop
  | swap (a b : α) (l : List α) : AdjacentSwap (a :: b :: l) (b :: a :: l)
  | cons (a : α) {l l' : List α} : AdjacentSwap l l' → AdjacentSwap (a :: l) (a :: l')

namespace AdjacentSwap

variable {α : Type}

theorem perm {l l' : List α} (h : AdjacentSwap l l') : List.Perm l l' := by
  induction h with
  | swap a b l => exact List.Perm.swap b a l
  | cons a _ ih => exact ih.cons a

theorem rtg_cons (a : α) {l l' : List α} (h : Relation.ReflTransGen AdjacentSwap l l') :
    Relation.ReflTransGen AdjacentSwap (a :: l) (a :: l') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.tail (cons a h)

end AdjacentSwap

/-- **Every permutation is a finite sequence of adjacent swaps** (and conversely). -/
theorem perm_iff_rtg_adjacentSwap {α : Type} {l l' : List α} :
    List.Perm l l' ↔ Relation.ReflTransGen AdjacentSwap l l' := by
  constructor
  · intro h
    induction h with
    | nil => exact Relation.ReflTransGen.refl
    | cons x _ ih => exact AdjacentSwap.rtg_cons x ih
    | swap x y l => exact Relation.ReflTransGen.single (AdjacentSwap.swap y x l)
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    induction h with
    | refl => exact List.Perm.refl _
    | tail _ h ih => exact ih.trans h.perm

/-- One adjacent swap of two argument slots of a category. -/
def ASPStep (C C' : Cat Atom) : Prop :=
  (flattenSpine C).1 = (flattenSpine C').1 ∧ AdjacentSwap (flattenSpine C).2 (flattenSpine C').2

theorem ASPStep.asp {C C' : Cat Atom} (h : ASPStep C C') : ASP C C' := ⟨h.1, h.2.perm⟩

theorem ASPStep.rtg_of_rtg_swap (a : Atom) {l l' : List (ArgSlot Atom)}
    (h : Relation.ReflTransGen AdjacentSwap l l') :
    Relation.ReflTransGen ASPStep (rebuildSpine (Cat.atom a) l) (rebuildSpine (Cat.atom a) l') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.tail ⟨by simp, by simpa [flatten_rebuild_atom] using h⟩

/-- **ASP is the reflexive–transitive closure of one local rule**: exchanging two adjacent
argument slots.  So ASP is not a schema of infinitely many primitive rules. -/
theorem ASP.iff_rtg_step {C C' : Cat Atom} : ASP C C' ↔ Relation.ReflTransGen ASPStep C C' := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨a, ha⟩ := flattenSpine_head_isAtom C
    have hC : C = rebuildSpine (Cat.atom a) (flattenSpine C).2 := by
      conv_lhs => rw [← rebuild_flatten C]
      rw [ha]
    have hC' : C' = rebuildSpine (Cat.atom a) (flattenSpine C').2 := by
      conv_lhs => rw [← rebuild_flatten C']
      rw [← h₁, ha]
    rw [hC, hC']
    exact ASPStep.rtg_of_rtg_swap a (perm_iff_rtg_adjacentSwap.mp h₂)
  · intro h
    induction h with
    | refl => exact ASP.refl _
    | tail _ h ih => exact ih.trans h.asp

/-! ### Rule sets with ASP (type raising switched **off**) -/

/-- Application only: FA and BA. -/
inductive App : Cat Atom → Cat Atom → Cat Atom → Prop
  | fa (X Y : Cat Atom) : App (X ⫽ Y) Y X
  | ba (X Y : Cat Atom) : App Y (X ⧵ Y) X

theorem App.toCombine {A B C : Cat Atom} (h : App A B C) : Combine A B C := by
  cases h with
  | fa => exact Combine.fa _ _
  | ba => exact Combine.ba _ _

namespace Rules

/-- FA + BA, no unary rules. -/
def app : Rules Atom := ⟨fun _ _ => False, App⟩
/-- `appAsp = FA + BA + ASP` (no TR). -/
def appAsp : Rules Atom := ⟨ASP, App⟩
/-- `appCompAsp = FA + BA + generalized composition + ASP` (no TR). -/
def appCompAsp : Rules Atom := ⟨ASP, Combine⟩

/-- The generic switch: add ASP as a unary rule to any rule set. -/
def withASP (R : Rules Atom) : Rules Atom := ⟨fun C D => R.unary C D ∨ ASP C D, R.bin⟩

theorem le_withASP (R : Rules Atom) : R ≤ R.withASP := ⟨fun _ _ h => Or.inl h, fun _ _ _ h => h⟩

theorem app_le_appAsp : (app : Rules Atom) ≤ appAsp := ⟨fun _ _ h => h.elim, fun _ _ _ h => h⟩
theorem appAsp_le_appCompAsp : (appAsp : Rules Atom) ≤ appCompAsp :=
  ⟨fun _ _ h => h, fun _ _ _ h => h.toCombine⟩
theorem noTR_le_appCompAsp : (noTR : Rules Atom) ≤ appCompAsp :=
  ⟨fun _ _ h => h.elim, fun _ _ _ h => h⟩
theorem appAsp_le_withASP_app : (appAsp : Rules Atom) ≤ app.withASP :=
  ⟨fun _ _ h => Or.inr h, fun _ _ _ h => h⟩
theorem withASP_app_le_appAsp : (app.withASP : Rules Atom) ≤ appAsp :=
  ⟨fun _ _ h => h.resolve_left id, fun _ _ _ h => h⟩
theorem appCompAsp_le_withASP_noTR : (appCompAsp : Rules Atom) ≤ noTR.withASP :=
  ⟨fun _ _ h => Or.inr h, fun _ _ _ h => h⟩
theorem withASP_noTR_le_appCompAsp : (noTR.withASP : Rules Atom) ≤ appCompAsp :=
  ⟨fun _ _ h => h.resolve_left id, fun _ _ _ h => h⟩

end Rules

end CCG
