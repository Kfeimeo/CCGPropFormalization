import CCGPropFormalization.Prediction
import CCGPropFormalization.Audit.ASF

/-!
# Audit 9 — GAC under the Transparent Modifier Assumption

System: `FA/BA + Bⁿ + ASP + AC + STR + D + GAC` (`Rules.fullLTR s`), sentences without
transparent modifiers (no `X/X`, `X\X` items).

**Positive coverage (machine-checked).**
* `John the man likes` — the motivating case for GAC (`lexDet_grammAcceptable`).
* `Read Mary's book` — the conjectured possessive counterexample dissolves: AC captures `Mary`,
  ASP rotates `(NP/N)\NP` to `(NP\NP)/N`, `B¹`, FA (`lexPoss_grammAcceptable`).
* `what apparently Mary likes` — with D and STR alone, no AC/ASP (`lexWhatApp_dStr`).

**New counterexample: root mismatch.**  STR pins the type-raising target to `S`, and every
prediction made by AC/GAC/D inherits that root.  A sentence whose root is a different atom `S'`
and whose subject must be raised is therefore stuck:

    John   Mary   loves-Q          NP  Q  (S'\NP)\Q   ⇒ S'      (an SOV yes/no question)

Every category of the prefix `John Mary` has head `S`, and no rule of the system can ever change
the head of the prefix state (`fullLTR_bin_head`), so `S'` is unreachable
(`lexSOVq_not_grammAcceptable`).  No transparent modifier is involved.
Replacing STR by goal-targeted raising `GTR S'` repairs it (`lexSOVq_grammAcceptable_goal`).
-/

namespace CCG

open Cat

variable {Atom : Type}

/-! ### Heads are preserved by every binary rule of the system -/

theorem ReplaceHead.head_left {A B F C : Cat Atom} (h : ReplaceHead A B F C) :
    (flattenSpine F).1 = (flattenSpine A).1 := by
  induction h with
  | refl => rfl
  | step s Z _ ih => simpa using ih

theorem ReplaceHead.head_right {A B F C : Cat Atom} (h : ReplaceHead A B F C) :
    (flattenSpine C).1 = (flattenSpine B).1 := by
  induction h with
  | refl => rfl
  | step s Z _ ih => simpa using ih

/-- A binary `Combine` step keeps the head of the functor: the left one (FA, forward
composition) or the right one (BA, backward composition; then the left constituent's head is the
head of the functor's argument). -/
theorem Combine.head {A B C : Cat Atom} (h : Combine A B C) :
    (flattenSpine C).1 = (flattenSpine A).1 ∨
    ((flattenSpine C).1 = (flattenSpine B).1 ∧
      ∃ X Y, B = X ⧵ Y ∧ (flattenSpine A).1 = (flattenSpine Y).1) := by
  rcases h.inv with ⟨X, Y, rfl, rfl, rfl⟩ | ⟨X, Y, rfl, rfl, rfl⟩ |
      ⟨X, Y, A', B', s', Z', hr, rfl, rfl, rfl⟩ | ⟨X, Y, A', B', s', Z', hr, rfl, rfl, rfl⟩
  · exact Or.inl (by simp)
  · exact Or.inr ⟨by simp, _, _, rfl, rfl⟩
  · exact Or.inl (by simp [hr.head_right])
  · exact Or.inr ⟨by simp [hr.head_right], _, _, rfl, by simp [hr.head_left]⟩

theorem AC.head {A B C : Cat Atom} (h : AC A B C) : (flattenSpine C).1 = (flattenSpine A).1 := by
  cases h; simp

theorem DComb.head {A B C : Cat Atom} (h : DComb A B C) :
    (flattenSpine C).1 = (flattenSpine A).1 := by
  cases h; simp

theorem GAC.head {A B C : Cat Atom} (h : GAC A B C) : (flattenSpine C).1 = (flattenSpine A).1 := by
  cases h with
  | gac hr => simp [hr.head_right]

/-- **Head invariant of the system**: a binary step keeps the head of the left constituent,
unless the right one is a backward functor whose argument has the head of the left one. -/
theorem fullLTR_bin_head {s : Atom} {A B C : Cat Atom} (h : (Rules.fullLTR s).bin A B C) :
    (flattenSpine C).1 = (flattenSpine A).1 ∨
    ((flattenSpine C).1 = (flattenSpine B).1 ∧
      ∃ X Y, B = X ⧵ Y ∧ (flattenSpine A).1 = (flattenSpine Y).1) := by
  rcases h with h | h | h | h
  · exact h.head
  · exact Or.inl h.head
  · exact Or.inl h.head
  · exact Or.inl h.head

/-- Unary steps (ASP, STR) never move the head away from `S`. -/
theorem fullLTR_rtg_head {s : Atom} {C₀ C : Cat Atom}
    (h : Relation.ReflTransGen (Rules.fullLTR s).unary C₀ C)
    (h₀ : (flattenSpine C₀).1 = atom s) : (flattenSpine C).1 = atom s := by
  induction h with
  | refl => exact h₀
  | tail _ h ih =>
    rcases h with h | h
    · rw [← h.head_eq]; exact ih
    · cases h; simp

/-- An atom on the left combines with nothing that is atomic or forward. -/
theorem fullLTR_atom_left {s : Atom} {a : Atom} {B C : Cat Atom} (h : (Rules.fullLTR s).bin (atom a) B C)
    (hB : (∃ b, B = atom b) ∨ ∃ X W, B = X ⫽ W) : False := by
  rcases h with h | h | h | h
  · rcases h.inv with ⟨X, Y, h₁, -, -⟩ | ⟨X, Y, -, h₂, -⟩ | ⟨_, _, _, _, _, _, -, h₁, -, -⟩ |
        ⟨_, _, _, _, _, _, -, h₁, -, -⟩
    · cases h₁
    · rcases hB with ⟨b, rfl⟩ | ⟨X', W, rfl⟩ <;> cases h₂
    · cases h₁
    · exact slash_ne_atom _ _ _ _ h₁.symm
  · cases h
  · cases h
  · cases h

section Examples

variable (s np n q s' : Atom)

local notation "S" => atom s
local notation "NP" => atom np
local notation "N" => atom n
local notation "Q" => atom q
local notation "S'" => atom s'
local notation "Rl" => Rules.fullLTR s

/-! ### Positive coverage -/

/-- `John the man likes` : `NP  NP/N  N  (S\NP)\NP`. -/
def lexDet : Fin 4 → Cat Atom := ![NP, NP ⫽ N, N, (S ⧵ NP) ⧵ NP]

/-- The GAC step `S/(S\NP), NP/N ⇒ (S/((S\NP)\NP))/N`. -/
theorem gac_det : GAC (S ⫽ (S ⧵ NP)) (NP ⫽ N) ((S ⫽ ((S ⧵ NP) ⧵ NP)) ⫽ N) :=
  GAC.gac (ReplaceHead.step .fwd N ReplaceHead.refl)

theorem lexDet_grammAcceptable : GrammAcceptable Rl (lexDet s np n) S := by
  intro i hi hin
  have john : Derives Rl (lexDet s np n) 0 1 (S ⫽ (S ⧵ NP)) :=
    (Derives.lex 0).unary (Or.inr (STR.str NP))
  have gac : (Rl).bin (S ⫽ (S ⧵ NP)) (NP ⫽ N) ((S ⫽ ((S ⧵ NP) ⧵ NP)) ⫽ N) :=
    Or.inr (Or.inr (Or.inr (gac_det s np n)))
  have fa₁ : (Rl).bin ((S ⫽ ((S ⧵ NP) ⧵ NP)) ⫽ N) N (S ⫽ ((S ⧵ NP) ⧵ NP)) :=
    Or.inl (Combine.fa _ _)
  have fa₂ : (Rl).bin (S ⫽ ((S ⧵ NP) ⧵ NP)) ((S ⧵ NP) ⧵ NP) S := Or.inl (Combine.fa _ _)
  obtain rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · exact ⟨NP, Derives.lex 0,
      (((Continues.refl.unary (Or.inr (STR.str NP))).bin (Derives.lex 1) gac).bin
        (Derives.lex 2) fa₁).bin (Derives.lex 3) fa₂⟩
  · exact ⟨_, john.bin (Derives.lex 1) gac, (Continues.refl.bin (Derives.lex 2) fa₁).bin (Derives.lex 3) fa₂⟩
  · exact ⟨_, (john.bin (Derives.lex 1) gac).bin (Derives.lex 2) fa₁, Continues.refl.bin (Derives.lex 3) fa₂⟩

/-- `Read Mary's book` : `S/NP  NP  (NP/N)\NP  N`. -/
def lexPoss : Fin 4 → Cat Atom := ![S ⫽ NP, NP, (NP ⫽ N) ⧵ NP, N]

theorem lexPoss_grammAcceptable : GrammAcceptable Rl (lexPoss s np n) S := by
  intro i hi hin
  have ac : (Rl).bin (S ⫽ NP) NP (S ⫽ (NP ⧵ NP)) := Or.inr (Or.inl (AC.ac S NP NP))
  have poss : Derives Rl (lexPoss s np n) 2 3 ((NP ⧵ NP) ⫽ N) :=
    (Derives.lex 2).unary (Or.inl (ASP.swap_outer NP .fwd N .bwd NP))
  have b₁ : (Rl).bin (S ⫽ (NP ⧵ NP)) ((NP ⧵ NP) ⫽ N) (S ⫽ N) := Or.inl (Combine.fcomp₁ S (NP ⧵ NP) N)
  have fa : (Rl).bin (S ⫽ N) N S := Or.inl (Combine.fa S N)
  obtain rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · exact ⟨_, Derives.lex 0, ((Continues.refl.bin (Derives.lex 1) ac).bin poss b₁).bin (Derives.lex 3) fa⟩
  · exact ⟨_, (Derives.lex 0).bin (Derives.lex 1) ac, (Continues.refl.bin poss b₁).bin (Derives.lex 3) fa⟩
  · exact ⟨_, ((Derives.lex 0).bin (Derives.lex 1) ac).bin poss b₁, Continues.refl.bin (Derives.lex 3) fa⟩

/-- `what apparently Mary likes` with D and STR only (no AC, no ASP): D absorbs `apparently`,
D again composes the raised subject into the argument, FA finishes. -/
theorem lexWhatApp_dStr : GrammAcceptable (Rules.dStr s) (lexWhatApp s np) S := by
  intro i hi hin
  have d₁ : (Rules.dStr s).bin (S ⫽ (S ⫽ NP)) (S ⫽ S) (S ⫽ (S ⫽ NP)) :=
    Or.inr (DComb.d S S NP S .fwd)
  have mary : Derives (Rules.dStr s) (lexWhatApp s np) 2 3 (S ⫽ (S ⧵ NP)) :=
    (Derives.lex 2).unary (STR.str NP)
  have d₂ : (Rules.dStr s).bin (S ⫽ (S ⫽ NP)) (S ⫽ (S ⧵ NP)) (S ⫽ ((S ⧵ NP) ⫽ NP)) :=
    Or.inr (DComb.d S S NP (S ⧵ NP) .fwd)
  have fa : (Rules.dStr s).bin (S ⫽ ((S ⧵ NP) ⫽ NP)) ((S ⧵ NP) ⫽ NP) S :=
    Or.inl (Combine.fa S ((S ⧵ NP) ⫽ NP))
  obtain rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · exact ⟨_, Derives.lex 0, ((Continues.refl.bin (Derives.lex 1) d₁).bin mary d₂).bin (Derives.lex 3) fa⟩
  · exact ⟨_, (Derives.lex 0).bin (Derives.lex 1) d₁, (Continues.refl.bin mary d₂).bin (Derives.lex 3) fa⟩
  · exact ⟨_, ((Derives.lex 0).bin (Derives.lex 1) d₁).bin mary d₂, Continues.refl.bin (Derives.lex 3) fa⟩

/-! ### The root-mismatch counterexample -/

/-- `John Mary loves-Q` : `NP  Q  (S'\NP)\Q`, root `S'`. -/
def lexSOVq : Fin 3 → Cat Atom := ![NP, Q, (S' ⧵ NP) ⧵ Q]

theorem lexSOVq_full : Derives Rules.noTR (lexSOVq np q s') 0 3 S' :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.lex 1) (Derives.lex 2) (Combine.ba (S' ⧵ NP) Q))
    (Combine.ba S' NP)

/-- No word of the sentence is a transparent modifier. -/
theorem lexSOVq_noTransparent : ∀ i, ¬ Transparent (lexSOVq np q s' i) := by
  intro i
  fin_cases i <;> rintro ⟨X, h | h⟩ <;> cases h

/-- Base predicate of the verb: itself or its ASP rotation. -/
def PV (C : Cat Atom) : Prop := C = (S' ⧵ NP) ⧵ Q ∨ C = (S' ⧵ Q) ⧵ NP

theorem PV_asp : ∀ C C', PV np q s' C → ASP C C' → PV np q s' C' := by
  rintro C C' (rfl | rfl) h
  · rcases ASP.eq_or_swap_of_two (a := s') (d₁ := .bwd) (d₂ := .bwd) h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rcases ASP.eq_or_swap_of_two (a := s') (d₁ := .bwd) (d₂ := .bwd) h with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

variable {s np q s'}

/-- The verb's unary closure. -/
theorem derivesQ23 {B : Cat Atom} (h : Derives Rl (lexSOVq np q s') 2 3 B) :
    B = (S' ⧵ NP) ⧵ Q ∨ B = (S' ⧵ Q) ⧵ NP ∨ ∃ W, B = S ⫽ W := by
  have h23 : (2 : ℕ) < 3 := by omega
  have h' : Relation.ReflTransGen (Rules.fullStrAC s).unary ((S' ⧵ NP) ⧵ Q) B := h.single rfl h23
  have hR : Raised s (PV np q s') B := rtg_raised s (PV_asp np q s') (Or.inl rfl) h'
  cases hR with
  | base h => exact h.imp id Or.inl
  | str => exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- Every category of the prefix `John Mary` has head `S`. -/
theorem derivesQ02_head {P : Cat Atom} (h : Derives Rl (lexSOVq np q s') 0 2 P) :
    (flattenSpine P).1 = S := by
  obtain ⟨A, B, P₀, hA, hB, hbin, hP₀⟩ := h.two rfl (by omega) (by omega)
  have hA' : Relation.ReflTransGen (Rules.fullStrAC s).unary NP A := hA
  have hB' : Relation.ReflTransGen (Rules.fullStrAC s).unary Q B := hB
  have hA : Raised s (PNP np) A := rtg_raised s (PNP_asp np) rfl hA'
  have hB : Raised s (PNP q) B := rtg_raised s (PNP_asp q) rfl hB'
  clear hA' hB'
  have hBform : (∃ b, B = atom b) ∨ ∃ X W, B = X ⫽ W := by
    cases hB with
    | base h => exact Or.inl ⟨q, h⟩
    | str => exact Or.inr ⟨_, _, rfl⟩
  have key : (flattenSpine P₀).1 = S := by
    cases hA with
    | base h => cases h; exact (fullLTR_atom_left hbin hBform).elim
    | @str Q₁ _ =>
      rcases fullLTR_bin_head hbin with h₁ | ⟨-, X, Y, hXY, -⟩
      · rw [h₁]; simp
      · rcases hBform with ⟨b, rfl⟩ | ⟨X', W, rfl⟩ <;> cases hXY
  exact fullLTR_rtg_head hP₀ key

/-- The head `S` of the prefix state survives every continuation step with the verb. -/
theorem continuesQ_head (hq : q ≠ s) (hnp : np ≠ s) {P : Cat Atom} {j : ℕ} {C : Cat Atom}
    (h : Continues Rl (lexSOVq np q s') 2 P j C) (hP : (flattenSpine P).1 = S) :
    (flattenSpine C).1 = S := by
  induction h with
  | refl => exact hP
  | unary _ hCD ih => exact fullLTR_rtg_head (Relation.ReflTransGen.single hCD) ih
  | @bin j k A B C _ hB hABC ih =>
    have hjk := hB.lt
    have hk := hB.le_n
    have hj : 2 ≤ j := Continues.le ‹_›
    obtain rfl : j = 2 := by omega
    obtain rfl : k = 3 := by omega
    rcases fullLTR_bin_head hABC with h₁ | ⟨-, X, Y, rfl, hAY⟩
    · rw [h₁]; exact ih
    · rcases derivesQ23 hB with h₂ | h₂ | ⟨W, h₂⟩
      · cases h₂; rw [ih] at hAY; exact absurd (Cat.atom.inj hAY) (Ne.symm hq)
      · cases h₂; rw [ih] at hAY; exact absurd (Cat.atom.inj hAY) (Ne.symm hnp)
      · cases h₂

/-- **Root mismatch**: the sentence derives `S'` with FA/BA alone, but under
`FA/BA + Bⁿ + ASP + AC + STR + D + GAC` no category of `John Mary` continues to `S'`. -/
theorem lexSOVq_not_grammAcceptable (hs : s' ≠ s) (hq : q ≠ s) (hnp : np ≠ s) :
    Derives Rules.noTR (lexSOVq np q s') 0 3 S' ∧ ¬ GrammAcceptable Rl (lexSOVq np q s') S' := by
  refine ⟨lexSOVq_full np q s', fun h => ?_⟩
  obtain ⟨P, hP, hC⟩ := h 2 (by omega) (by omega)
  have := continuesQ_head hq hnp hC (derivesQ02_head hP)
  exact hs (Cat.atom.inj this)

/-! ### The repair: goal-targeted type raising -/

/-- With `GTR S'` the same sentence is grammatically acceptable. -/
theorem lexSOVq_grammAcceptable_goal :
    GrammAcceptable (Rules.fullLTRg S') (lexSOVq np q s') S' := by
  intro i hi hin
  have ac : (Rules.fullLTRg S').bin (S' ⫽ (S' ⧵ NP)) Q (S' ⫽ ((S' ⧵ NP) ⧵ Q)) :=
    Or.inr (Or.inl (AC.ac S' (S' ⧵ NP) Q))
  have fa : (Rules.fullLTRg S').bin (S' ⫽ ((S' ⧵ NP) ⧵ Q)) ((S' ⧵ NP) ⧵ Q) S' :=
    Or.inl (Combine.fa _ _)
  obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
  · exact ⟨_, Derives.lex 0,
      ((Continues.refl.unary (Or.inr (GTR.gtr NP))).bin (Derives.lex 1) ac).bin (Derives.lex 2) fa⟩
  · exact ⟨_, ((Derives.lex 0).unary (Or.inr (GTR.gtr NP))).bin (Derives.lex 1) ac,
      Continues.refl.bin (Derives.lex 2) fa⟩

/-- …and with clause-type targets `[S, S']` (the enumerator's setting) via monotonicity. -/
theorem lexSOVq_grammAcceptable_clause :
    GrammAcceptable (Rules.fullLTRs [S, S']) (lexSOVq np q s') S' := by
  intro i hi hin
  obtain ⟨P, hP, hC⟩ := lexSOVq_grammAcceptable_goal i hi hin
  have hle := Rules.fullLTRg_le_fullLTRs S' [S, S'] (by simp)
  exact ⟨P, hP.mono hle, hC.mono hle⟩

end Examples

end CCG
