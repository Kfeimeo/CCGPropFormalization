import CCGPropFormalization.Positive

/-!
# Audit 2 — the *strong* (same-category / reassociation) version is false

`Positive.lean` shows that prefix reducibility holds for a trivial reason.  The natural
non-trivial strengthening — "the prefix categories can be chosen *compatible* with the full
derivation", equivalently "every derivation can be reassociated into a left-branching derivation
**of the same category**" — is **false**, even with unrestricted (forward and backward) type
raising at every node, generalized (possibly crossed) forward composition **and** generalized
backward composition.

Counterexample (`n = 3`, object extraction "what John likes"):

  `w₁ = S/(S/NP)`,  `w₂ = NP`,  `w₃ = (S\NP)/NP`

Right-branching derivation of `S`:  `NP ⇒ S/(S\NP)` (TR), `S/(S\NP)  (S\NP)/NP ⇒ S/NP` (`B¹`),
`S/(S/NP)  S/NP ⇒ S` (FA).

There is **no** left-branching derivation of `S`, and more generally no way to split the sentence
as `(w₁ w₂) w₃` with the two pieces combining to `S`.  The proof is a finite case analysis on the
last rule plus three inductions along the type-raising closure (`TRStar`).
-/

namespace CCG

open Cat

variable {Atom : Type}

/-- Reflexive–transitive closure of unrestricted type raising. -/
abbrev TRStar : Cat Atom → Cat Atom → Prop := Relation.ReflTransGen TypeRaise

/-- Only an atom can type-raise (zero or more times) to that atom. -/
theorem TRStar.eq_of_atom {A : Cat Atom} {a : Atom} (h : TRStar A (atom a)) : A = atom a := by
  rcases h.cases_tail with h | ⟨_, -, hc⟩
  · exact h.symm
  · exact absurd rfl (hc.ne_atom a)

section WhatJohnLikes

variable (s np : Atom)

local notation "S" => atom s
local notation "NP" => atom np

/-- The lexicon `[S/(S/NP), NP, (S\NP)/NP]` — "what John likes". -/
def lexWhat : Fin 3 → Cat Atom := ![S ⫽ (S ⫽ NP), NP, (S ⧵ NP) ⫽ NP]

/-- The right-branching derivation `what (John likes) ⇒ S`. -/
theorem lexWhat_full : Derives Rules.full (lexWhat s np) 0 3 S :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.tr (Derives.lex 1) (TypeRaise.fwd S NP)) (Derives.lex 2)
      (Combine.fcomp₁ S (S ⧵ NP) NP))
    (Combine.fa S (S ⫽ NP))

/-- No type-raised `NP` has the shape `Y'/u` with `u` a type-raised `(S\NP)/NP`. -/
theorem lexWhat_aux_np {B : Cat Atom} (hB : TRStar NP B) :
    ∀ Y' u, TRStar ((S ⧵ NP) ⫽ NP) u → B ≠ Y' ⫽ u := by
  induction hB with
  | refl => intro _ _ _ h; cases h
  | tail _ hTR ih =>
    intro Y' u hu h
    cases hTR with
    | fwd T A =>
      cases h
      rcases hu.cases_tail with h' | ⟨u'', hu'', hTR'⟩
      · cases h'
      · cases hTR' with
        | bwd => exact ih _ _ hu'' rfl
    | bwd => cases h

/-- No type-raised `S/(S/NP)` has the shape `(S/u)/B` with `B` a type-raised `NP` and
`u` a type-raised `(S\NP)/NP`. -/
theorem lexWhat_aux_a₁ {A : Cat Atom} (hA : TRStar (S ⫽ (S ⫽ NP)) A) :
    ∀ B u, TRStar NP B → TRStar ((S ⧵ NP) ⫽ NP) u → A ≠ (S ⫽ u) ⫽ B := by
  induction hA with
  | refl => intro _ _ _ _ h; cases h
  | tail _ hTR ih =>
    intro B u hB hu h
    cases hTR with
    | fwd T A₃ =>
      cases h
      rcases hB.cases_tail with h' | ⟨B₃, hB₃, hTR'⟩
      · cases h'
      · cases hTR' with
        | bwd => exact ih _ _ hB₃ hu rfl
    | bwd => cases h

/-- No type-raised `S/(S/NP)` has the shape `(S/B)/u` with `B` a type-raised `NP` and
`u` a type-raised `(S\NP)/NP`. -/
theorem lexWhat_aux_a₂ {A : Cat Atom} (hA : TRStar (S ⫽ (S ⫽ NP)) A) :
    ∀ B u, TRStar NP B → TRStar ((S ⧵ NP) ⫽ NP) u → A ≠ (S ⫽ B) ⫽ u := by
  induction hA with
  | refl => intro _ _ _ _ h; cases h
  | tail _ hTR ih =>
    intro B u hB hu h
    cases hTR with
    | fwd T A₃ =>
      cases h
      rcases hu.cases_tail with h' | ⟨u'', hu'', hTR'⟩
      · cases h'
      · cases hTR' with
        | bwd => exact ih _ _ hB hu'' rfl
    | bwd => cases h

/-- "Good" categories are those of the form `S/u` with `u` a type-raised `(S\NP)/NP`:
exactly the categories that can still combine with (a type-raised) `w₃` to give `S`.
Goodness is preserved backwards along type raising. -/
theorem lexWhat_good_of_trstar {P₀ P : Cat Atom} (h : TRStar P₀ P)
    (hP : ∃ u, TRStar ((S ⧵ NP) ⫽ NP) u ∧ P = S ⫽ u) :
    ∃ u, TRStar ((S ⧵ NP) ⫽ NP) u ∧ P₀ = S ⫽ u := by
  induction h with
  | refl => exact hP
  | tail _ hTR ih =>
    apply ih
    obtain ⟨u, hu, hP⟩ := hP
    cases hTR with
    | fwd T A₃ =>
      cases hP
      rcases hu.cases_tail with h' | ⟨u'', hu'', hTR'⟩
      · cases h'
      · cases hTR' with
        | bwd => exact ⟨_, hu'', rfl⟩
    | bwd => cases hP

/-- Combining a type-raised `w₁` with a type-raised `w₂` by **any** binary rule never yields a
good category. -/
theorem lexWhat_not_good_combine {A B P : Cat Atom}
    (hA : TRStar (S ⫽ (S ⫽ NP)) A) (hB : TRStar NP B) (hC : Combine A B P) :
    ¬ ∃ u, TRStar ((S ⧵ NP) ⫽ NP) u ∧ P = S ⫽ u := by
  rintro ⟨u, hu, rfl⟩
  rcases hC.inv with ⟨X, Y, hA', hB', hX⟩ | ⟨X, Y, hA', hB', hX⟩ |
      ⟨X, Y, A', B', s', Z, hr, hA', hB', hX⟩ | ⟨X, Y, A', B', s', Z, hr, hA', hB', hX⟩
  · -- FA: `A = (S/u)/B`
    subst hX hB' hA'
    exact lexWhat_aux_a₁ s np hA _ _ hB hu rfl
  · -- BA: `B = (S/u)\A`, so `B = T\(T/B₃)` with `A = (S/u)/B₃`
    subst hX hA' hB'
    rcases hB.cases_tail with h' | ⟨B₃, hB₃, hTR'⟩
    · cases h'
    · cases hTR' with
      | bwd => exact lexWhat_aux_a₁ s np hA _ _ hB₃ hu rfl
  · -- forward composition: the spine must be exactly `/u` and the head `S`, so `B = Y/u`
    rw [eq_comm, slash_eq_fwd_iff] at hX
    obtain ⟨rfl, rfl, rfl⟩ := hX
    obtain ⟨rfl, rfl⟩ := hr.eq_of_atom rfl
    subst hA' hB'
    exact lexWhat_aux_np s np hB _ _ hu rfl
  · -- backward composition: the spine is `/u`, head `S`, so `B = S\Y = T\(T/B₃)`, `A = (S/B₃)/u`
    rw [eq_comm, slash_eq_fwd_iff] at hX
    obtain ⟨rfl, rfl, rfl⟩ := hX
    obtain ⟨rfl, rfl⟩ := hr.eq_of_atom rfl
    subst hA' hB'
    rcases hB.cases_tail with h' | ⟨B₃, hB₃, hTR'⟩
    · cases h'
    · cases hTR' with
      | bwd => exact lexWhat_aux_a₂ s np hA _ _ hB₃ hu rfl

/-- **Main negative result.**  The sentence cannot be split as `(w₁ w₂) w₃` with the two pieces
combining to `S`: no category of the prefix `what John` is compatible with the final `S`. -/
theorem lexWhat_no_compatible_prefix :
    ¬ ∃ P D, Derives Rules.full (lexWhat s np) 0 2 P ∧ Derives Rules.full (lexWhat s np) 2 3 D ∧
      Combine P D S := by
  rintro ⟨P, D, hP, hD, hC⟩
  obtain ⟨A, B, P₀, hA, hB, hbin, hP₀⟩ := hP.two rfl (by omega) (by omega)
  have hA : TRStar (S ⫽ (S ⫽ NP)) A := hA
  have hB : TRStar NP B := hB
  have h23 : 2 < 3 := by omega
  have hD : TRStar ((S ⧵ NP) ⫽ NP) D := hD.single rfl h23
  have hP₀ : TRStar P₀ P := hP₀
  apply lexWhat_not_good_combine s np hA hB hbin
  apply lexWhat_good_of_trstar s np hP₀
  rcases hC.inv with ⟨X, Y, hP', hD', hX⟩ | ⟨X, Y, hP', hD', hX⟩ |
      ⟨_, _, _, _, _, _, _, _, _, hX⟩ | ⟨_, _, _, _, _, _, _, _, _, hX⟩
  · subst hX hP' hD'
    exact ⟨_, hD, rfl⟩
  · subst hX hP' hD'
    rcases hD.cases_tail with h' | ⟨D'', hD'', hTR'⟩
    · cases h'
    · cases hTR' with
      | bwd => exact ⟨_, hD'', rfl⟩
  · exact absurd hX.symm (slash_ne_atom _ _ _ _)
  · exact absurd hX.symm (slash_ne_atom _ _ _ _)

/-- Strong prefix reducibility fails for "what John likes". -/
theorem lexWhat_not_strongPrefixReducible :
    ¬ StrongPrefixReducible Rules.full (lexWhat s np) S :=
  fun h => lexWhat_no_compatible_prefix s np (h 2 (by omega) (by omega))

/-- **Strong normalization fails**: `S` is derivable, but not by any left-branching derivation. -/
theorem lexWhat_no_leftSpine : ¬ LeftSpine Rules.full (lexWhat s np) 0 3 S := by
  intro h
  rcases h.inv with ⟨-, hj, -⟩ | ⟨k, A, B, C₀, hk, h₁, h₂, hbin, hC⟩
  · omega
  · obtain rfl : k = 2 := by omega
    have hC : TRStar C₀ S := hC
    obtain rfl := hC.eq_of_atom
    exact lexWhat_no_compatible_prefix s np ⟨A, B, h₁.toDerives, h₂.toDerives, hbin⟩

/-- Summary: `Derives lex 0 n C → LeftSpine lex 0 n C` is **false** in the full system. -/
theorem not_strong_left_spine_normalization :
    Derives Rules.full (lexWhat s np) 0 3 S ∧ ¬ LeftSpine Rules.full (lexWhat s np) 0 3 S :=
  ⟨lexWhat_full s np, lexWhat_no_leftSpine s np⟩

end WhatJohnLikes

end CCG
