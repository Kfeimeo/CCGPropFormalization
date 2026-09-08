import CCGPropFormalization.Audit.STR

/-!
# Prediction rules: D, GAC, goal-targeted TR, and the Transparent Modifier Assumption

* `DComb` — the D combinator (Hoyt & Baldridge): `X/(Y|Z), Y/W ⇒ X/(W|Z)`, composition *into*
  the argument of a forward functor.
* `GAC` — generalized argument capture: `X/Y, A|Z₁…|Zₙ ⇒ (X/(Y\A))|Z₁…|Zₙ`, i.e. the head `A`
  of the right functor is captured, its spine is kept.  `n = 0` is `AC`; in general it is
  "type-raise the head to target `Y`, then `Bⁿ⁺¹`" (`GAC.headTR_comp`).
* `GTR g` — type raising whose target is the parse goal `g`: `X ⇒ g/(g\X)`.  `STR s = GTR (atom s)`.
* `Transparent`, `πsyn`, `WellMarked` — the Transparent Modifier Assumption: lexically *marked*
  items of shape `X/X` or `X\X` are projected out of the syntactic sequence.
* Rule sets `Rules.fullLTR s` (FA/BA + Bⁿ + ASP + AC + STR + D + GAC) and `Rules.fullLTRg g`
  (the same with `GTR g` instead of `STR`).
-/

namespace CCG

open Cat

variable {Atom : Type}

/-- The D combinator: `X/(Y|Z), Y/W ⇒ X/(W|Z)` (inner slash `|` preserved). -/
inductive DComb : Cat Atom → Cat Atom → Cat Atom → Prop
  | d (X Y Z W : Cat Atom) (dz : Slash) :
      DComb (X ⫽ (Y.slash dz Z)) (Y ⫽ W) (X ⫽ (W.slash dz Z))

/-- Generalized argument capture: `C` is `F` with its head `A` replaced by `X/(Y\A)`. -/
inductive GAC : Cat Atom → Cat Atom → Cat Atom → Prop
  | gac {X Y A F C : Cat Atom} : ReplaceHead A (X ⫽ (Y ⧵ A)) F C → GAC (X ⫽ Y) F C

/-- `AC` is `GAC` with an empty spine. -/
theorem GAC.of_ac {A B C : Cat Atom} (h : AC A B C) : GAC A B C := by
  cases h; exact GAC.gac ReplaceHead.refl

/-- **GAC = head type raising (target `Y`) + generalized composition.**  The head `A` of `F` is
raised to `Y/(Y\A)` (spine kept), and `X/Y` composes with the result. -/
theorem GAC.headTR_comp {X Y F C : Cat Atom} (h : GAC (X ⫽ Y) F C) :
    ∃ A F', ReplaceHead A (Y ⫽ (Y ⧵ A)) F F' ∧ Combine (X ⫽ Y) F' C := by
  cases h with
  | @gac X Y A F C hr =>
    obtain ⟨sp, rfl, rfl⟩ := ReplaceHead.iff_spine.mp hr
    refine ⟨A, (Y ⫽ (Y ⧵ A)).spine sp, ReplaceHead.iff_spine.mpr ⟨sp, rfl, rfl⟩, ?_⟩
    have e₁ : (Y ⫽ (Y ⧵ A)).spine sp = Y.spine (sp ++ [(.fwd, Y ⧵ A)]) := by
      rw [Cat.spine_append]; rfl
    have e₂ : (X ⫽ (Y ⧵ A)).spine sp = X.spine (sp ++ [(.fwd, Y ⧵ A)]) := by
      rw [Cat.spine_append]; rfl
    rw [e₁, e₂]
    cases sp with
    | nil => exact Combine.fcomp .fwd (Y ⧵ A) ReplaceHead.refl
    | cons p sp' =>
      obtain ⟨s, Z⟩ := p
      simp only [List.cons_append, Cat.spine_cons]
      exact Combine.fcomp s Z (ReplaceHead.iff_spine.mpr ⟨_, rfl, rfl⟩)

/-- Goal-targeted type raising: `X ⇒ g/(g\X)`. -/
inductive GTR (g : Cat Atom) : Cat Atom → Cat Atom → Prop
  | gtr (X : Cat Atom) : GTR g X (g ⫽ (g ⧵ X))

theorem STR.gtr {s : Atom} {X Y : Cat Atom} (h : STR s X Y) : GTR (atom s) X Y := by
  cases h; exact GTR.gtr _

/-! ### Transparent Modifier Assumption -/

/-- A category of shape `X/X` or `X\X`. -/
def Transparent (C : Cat Atom) : Prop := ∃ X, C = X ⫽ X ∨ C = X ⧵ X

variable {n : ℕ}

/-- Syntactic projection: erase the marked items, keep the rest in order. -/
def πsyn (lex : Fin n → Cat Atom) (mark : Fin n → Bool) : List (Cat Atom) :=
  ((List.finRange n).filter (fun i => !mark i)).map lex

/-- Only transparent items may be marked. -/
def WellMarked (lex : Fin n → Cat Atom) (mark : Fin n → Bool) : Prop :=
  ∀ i, mark i = true → Transparent (lex i)

/-- Nothing marked: the projection is the sentence itself. -/
theorem πsyn_unmarked (lex : Fin n → Cat Atom) : πsyn lex (fun _ => false) = List.ofFn lex := by
  simp [πsyn, List.ofFn_eq_map]

/-- A lexicon without transparent items is trivially well marked by the empty marking. -/
theorem wellMarked_none (lex : Fin n → Cat Atom) : WellMarked lex (fun _ => false) :=
  fun _ h => by cases h

/-! ### Rule sets -/

namespace Rules

/-- FA/BA + Bⁿ + ASP + AC + STR + D + GAC. -/
def fullLTR (s : Atom) : Rules Atom :=
  ⟨fun C D => ASP C D ∨ STR s C D,
   fun A B C => Combine A B C ∨ AC A B C ∨ DComb A B C ∨ GAC A B C⟩

/-- The same with goal-targeted type raising. -/
def fullLTRg (g : Cat Atom) : Rules Atom :=
  ⟨fun C D => ASP C D ∨ GTR g C D,
   fun A B C => Combine A B C ∨ AC A B C ∨ DComb A B C ∨ GAC A B C⟩

/-- Only D and STR (no AC, no ASP, no GAC): enough for the extraction examples. -/
def dStr (s : Atom) : Rules Atom :=
  ⟨STR s, fun A B C => Combine A B C ∨ DComb A B C⟩

theorem fullLTR_le_fullLTRg (s : Atom) : fullLTR s ≤ (fullLTRg (atom s) : Rules Atom) :=
  ⟨fun _ _ h => h.imp id STR.gtr, fun _ _ _ h => h⟩

theorem dStr_le_fullLTR (s : Atom) : dStr s ≤ (fullLTR s : Rules Atom) :=
  ⟨fun _ _ h => Or.inr h, fun _ _ _ h => h.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))⟩

theorem fullStrAC_le_fullLTR (s : Atom) : fullStrAC s ≤ (fullLTR s : Rules Atom) :=
  ⟨fun _ _ h => h, fun _ _ _ h => h.elim Or.inl (fun h => Or.inr (Or.inl h))⟩

end Rules

end CCG
