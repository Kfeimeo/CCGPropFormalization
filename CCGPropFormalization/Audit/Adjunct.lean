import CCGPropFormalization.Audit.STR

/-!
# Audit 6 (continued) — grammatical acceptability fails: right adjunction

    John likes Mary madly  :  NP  (S\NP)/NP  NP  (S\NP)\(S\NP)

The sentence derives `S` with FA/BA alone (`lexAdj_full`).  Under the full system
`FA/BA + Bⁿ + ASP + AC + STR` the prefix `John likes` reduces to plenty of categories — but
each of them is `S/Z` for a `Z` that the suffix `Mary madly` cannot supply, in any bracketing.

Proof architecture:
1. `Raised P` — iterated STR over a base predicate `P` closed under ASP; the unary closure of
   every word is of this form (`rtg_raised`);
2. the categories of `[0,2)`, `[2,3)`, `[2,4)`, `[3,4)` (`derives02`, `derives24`, …);
3. an invariant `Inv j C` on continuation states `(j, C)` (`NotBad` records what the residual
   argument `Z` of `S/Z` can never be), preserved by every unary and binary step;
4. `Inv 4 S` is false.
-/

namespace CCG

open Cat

variable {Atom : Type}

/-- A permutation of a two-element list is the list or its swap. -/
theorem perm_pair {α : Type} {a b : α} {l : List α} (h : List.Perm [a, b] l) :
    l = [a, b] ∨ l = [b, a] := by
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp (h.length_eq.symm)
  have ha : a ∈ [x, y] := h.subset (by simp)
  rcases List.mem_cons.mp ha with rfl | hy
  · have := List.perm_singleton.mp h.cons_inv
    cases this; exact Or.inl rfl
  · have hay : a = y := by simpa using hy
    subst hay
    have := List.perm_singleton.mp (h.trans (List.Perm.swap a x [])).cons_inv
    cases this; exact Or.inr rfl

/-- ASP on a two-slot category with atomic head: identity or the swap. -/
theorem ASP.eq_or_swap_of_two {a : Atom} {d₁ d₂ : Dir} {A B C' : Cat Atom}
    (h : ASP (((atom a).slash d₁ A).slash d₂ B) C') :
    C' = ((atom a).slash d₁ A).slash d₂ B ∨ C' = ((atom a).slash d₂ B).slash d₁ A := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [flattenSpine_slash, flattenSpine_atom, List.nil_append, List.singleton_append] at h₁ h₂
  have hC := rebuild_flatten C'
  rw [← h₁] at hC
  rcases perm_pair h₂ with h₃ | h₃ <;> rw [h₃] at hC
  · exact Or.inl hC.symm
  · exact Or.inr hC.symm

section Adjunct

variable (s np : Atom)

local notation "S" => atom s
local notation "NP" => atom np
local notation "Rf" => Rules.fullStrAC s

/-- Iterated S-targeted type raising on top of a base predicate. -/
inductive Raised (P : Cat Atom → Prop) : Cat Atom → Prop
  | base {C : Cat Atom} : P C → Raised P C
  | str {Q : Cat Atom} : Raised P Q → Raised P (S ⫽ (S ⧵ Q))

/-- The unary closure (`ASP ∨ STR`) of `C₀` is `Raised P` whenever `P C₀` and `P` is closed
under ASP. -/
theorem rtg_raised {P : Cat Atom → Prop} (hP : ∀ C C', P C → ASP C C' → P C')
    {C₀ C : Cat Atom} (h₀ : P C₀) (h : Relation.ReflTransGen (Rf).unary C₀ C) : Raised s P C := by
  induction h with
  | refl => exact Raised.base h₀
  | tail _ h ih =>
    rcases h with h | h
    · cases ih with
      | base hp => exact Raised.base (hP _ _ hp h)
      | str hQ => rw [h.eq_of_atom_fwd]; exact Raised.str hQ
    · cases h; exact Raised.str ih

/-- Base predicates for the four words. -/
def PNP (C : Cat Atom) : Prop := C = NP
def PLikes (C : Cat Atom) : Prop := C = (S ⧵ NP) ⫽ NP ∨ C = (S ⫽ NP) ⧵ NP
def PMadly (C : Cat Atom) : Prop := C = (S ⧵ NP) ⧵ (S ⧵ NP) ∨ C = (S ⧵ (S ⧵ NP)) ⧵ NP
def PEq (C₀ C : Cat Atom) : Prop := C = C₀

theorem PNP_asp : ∀ C C', PNP np C → ASP C C' → PNP np C' := by
  rintro C C' rfl h; exact h.eq_of_atom

theorem PLikes_asp : ∀ C C', PLikes s np C → ASP C C' → PLikes s np C' := by
  rintro C C' (rfl | rfl) h
  · rcases ASP.eq_or_swap_of_two (a := s) (d₁ := .bwd) (d₂ := .fwd) h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rcases ASP.eq_or_swap_of_two (a := s) (d₁ := .fwd) (d₂ := .bwd) h with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

theorem PMadly_asp : ∀ C C', PMadly s np C → ASP C C' → PMadly s np C' := by
  rintro C C' (rfl | rfl) h
  · rcases ASP.eq_or_swap_of_two (a := s) (d₁ := .bwd) (d₂ := .bwd) h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rcases ASP.eq_or_swap_of_two (a := s) (d₁ := .bwd) (d₂ := .bwd) h with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

theorem PEq_asp {C₀ : Cat Atom} (h₀ : spineLength C₀ ≤ 1) :
    ∀ C C', PEq C₀ C → ASP C C' → PEq C₀ C' := by
  rintro C C' rfl h; exact h.eq_of_spineLength_le_one h₀

/-- `John likes Mary madly`. -/
def lexAdj : Fin 4 → Cat Atom := ![NP, (S ⧵ NP) ⫽ NP, NP, (S ⧵ NP) ⧵ (S ⧵ NP)]

/-- The sentence derives `S` by application alone: `John ((likes Mary) madly)`. -/
theorem lexAdj_full : Derives Rules.app (lexAdj s np) 0 4 S :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.bin (Derives.lex 1) (Derives.lex 2) (App.fa (S ⧵ NP) NP))
      (Derives.lex 3) (App.ba (S ⧵ NP) (S ⧵ NP)))
    (App.ba S NP)

/-- What the residual argument `Z` of a prefix category `S/Z` can never be. -/
structure NotBad (Z : Cat Atom) : Prop where
  ne_S : Z ≠ S
  ne_adv : Z ≠ (S ⧵ NP) ⧵ (S ⧵ NP)
  ne_advS : Z ≠ (S ⧵ (S ⧵ NP)) ⧵ NP
  ne_SVP : Z ≠ S ⧵ (S ⧵ NP)
  ne_VP : Z ≠ S ⧵ NP
  ne_fwd : ∀ W, Z ≠ S ⫽ W

/-- Continuation-state invariant. -/
def Inv (j : ℕ) (C : Cat Atom) : Prop :=
  (j = 2 ∧ ∃ Z, C = S ⫽ Z ∧ NotBad s np Z) ∨
  (j = 3 ∧ (C = S ∨ ∃ Z, C = S ⫽ Z ∧ NotBad s np Z)) ∨
  (j = 4 ∧ ∃ Z, C = S ⫽ Z)

variable {s np}

theorem Raised.fwd {P : Cat Atom → Prop} (hP : ∀ C, P C → ∃ W, C = S ⫽ W) {C : Cat Atom}
    (h : Raised s P C) : ∃ W, C = S ⫽ W := by
  cases h with
  | base h => exact hP _ h
  | str => exact ⟨_, rfl⟩

theorem NotBad.ofNP (hsn : np ≠ s) : NotBad s np NP where
  ne_S h := hsn (Cat.atom.inj h)
  ne_adv h := by cases h
  ne_advS h := by cases h
  ne_SVP h := by cases h
  ne_VP h := by cases h
  ne_fwd _ h := by cases h

/-- `Z = S\C` for a state `C ∈ {S} ∪ {S/Z'}` (the STR step). -/
theorem NotBad.str (hsn : np ≠ s) {C : Cat Atom} (hC : C = S ∨ ∃ Z, C = S ⫽ Z) :
    NotBad s np (S ⧵ C) where
  ne_S h := by cases h
  ne_adv h := by cases h
  ne_advS h := by cases h
  ne_SVP h := by rcases hC with rfl | ⟨Z, rfl⟩ <;> cases h
  ne_VP h := by
    rcases hC with rfl | ⟨Z, rfl⟩
    · exact hsn (Cat.atom.inj (Cat.bwd.inj h).2).symm
    · cases h
  ne_fwd _ h := by cases h

/-- `Z = Z₀\B` (the AC step). -/
theorem NotBad.ac {Z : Cat Atom} (hZ : NotBad s np Z) (B : Cat Atom) : NotBad s np (Z ⧵ B) where
  ne_S h := by cases h
  ne_adv h := hZ.ne_VP (Cat.bwd.inj h).1
  ne_advS h := hZ.ne_SVP (Cat.bwd.inj h).1
  ne_SVP h := hZ.ne_S (Cat.bwd.inj h).1
  ne_VP h := hZ.ne_S (Cat.bwd.inj h).1
  ne_fwd _ h := by cases h

/-- `Z = (S\Q)\L` (AC of a raised `John` over a form of `likes`). -/
theorem NotBad.acLikes {Q L : Cat Atom} (hQ : Raised s (PNP np) Q) (hL : Raised s (PLikes s np) L) :
    NotBad s np ((S ⧵ Q) ⧵ L) where
  ne_S h := by cases h
  ne_adv h := by
    cases hL with
    | base hL => rcases hL with rfl | rfl <;> cases h
    | str => cases h
  ne_advS h := by
    cases hQ with
    | base hQ => cases hQ; cases h
    | str => cases h
  ne_SVP h := by cases h
  ne_VP h := by cases h
  ne_fwd _ h := by cases h

/-! ### Categories of the spans -/

/-- `[2,3)` (`Mary`) and its raisings. -/
theorem derives23 {B : Cat Atom} (h : Derives Rf (lexAdj s np) 2 3 B) : Raised s (PNP np) B := by
  have h24 : (2 : ℕ) < 4 := by omega
  have h' : Relation.ReflTransGen (Rf).unary NP B := h.single rfl h24
  exact rtg_raised s (PNP_asp np) rfl h'

/-- `[3,4)` (`madly`) and its raisings. -/
theorem derives34 {B : Cat Atom} (h : Derives Rf (lexAdj s np) 3 4 B) :
    Raised s (PMadly s np) B := by
  have h34 : (3 : ℕ) < 4 := by omega
  have h' : Relation.ReflTransGen (Rf).unary ((S ⧵ NP) ⧵ (S ⧵ NP)) B := h.single rfl h34
  exact rtg_raised s (PMadly_asp s np) (Or.inl rfl) h'

/-- `[0,2)` (`John likes`): always `S/Z` with `Z` not bad. -/
theorem derives02 (hsn : np ≠ s) {P : Cat Atom} (h : Derives Rf (lexAdj s np) 0 2 P) :
    ∃ Z, P = S ⫽ Z ∧ NotBad s np Z := by
  obtain ⟨A, B, P₀, hA, hB, hbin, hP₀⟩ := h.two rfl (by omega) (by omega)
  have hA' : Relation.ReflTransGen (Rf).unary NP A := hA
  have hB' : Relation.ReflTransGen (Rf).unary ((S ⧵ NP) ⫽ NP) B := hB
  have hA : Raised s (PNP np) A := rtg_raised s (PNP_asp np) rfl hA'
  have hB : Raised s (PLikes s np) B := rtg_raised s (PLikes_asp s np) (Or.inl rfl) hB'
  clear hA' hB'
  -- Step 1: the one binary step gives `S/Z₀` with `Z₀` not bad.
  have key : ∃ Z, P₀ = S ⫽ Z ∧ NotBad s np Z := by
    rcases hbin with hc | hc
    · rcases hc.inv with ⟨X, Y, rfl, rfl, rfl⟩ | ⟨X, Y, rfl, rfl, rfl⟩ |
          ⟨X, Y, A', B', s', Z', hr, rfl, hB', rfl⟩ | ⟨X, Y, A', B', s', Z', hr, hA', rfl, rfl⟩
      · -- FA
        cases hA with
        | base h => cases h
        | str hQ =>
          cases hB with
          | base h => rcases h with h | h <;> cases h
      · -- BA
        cases hB with
        | base h =>
          rcases h with h | h
          · cases h
          · cases h
            cases hA with
            | base h => cases h; exact ⟨NP, rfl, NotBad.ofNP hsn⟩
      · -- forward composition
        cases hA with
        | base h => cases h
        | @str Q hQ =>
          cases hB with
          | base h =>
            rcases h with rfl | rfl
            · rw [eq_comm, slash_eq_fwd_iff] at hB'
              obtain ⟨rfl, rfl, rfl⟩ := hB'
              rcases hr.inv with ⟨h₁, rfl⟩ | ⟨s'', Z'', A'', B'', hr', h₁, -⟩
              · cases h₁; exact ⟨NP, rfl, NotBad.ofNP hsn⟩
              · rw [eq_comm, slash_eq_bwd_iff] at h₁
                obtain ⟨rfl, rfl, rfl⟩ := h₁
                obtain ⟨h₂, -⟩ := hr'.atom_left rfl
                cases h₂
            · rw [eq_comm, slash_eq_bwd_iff] at hB'
              obtain ⟨rfl, rfl, rfl⟩ := hB'
              rcases hr.inv with ⟨h₁, -⟩ | ⟨s'', Z'', A'', B'', hr', h₁, -⟩
              · cases h₁
              · rw [eq_comm, slash_eq_fwd_iff] at h₁
                obtain ⟨rfl, rfl, rfl⟩ := h₁
                obtain ⟨h₂, -⟩ := hr'.atom_left rfl
                cases h₂
          | str =>
            rw [eq_comm, slash_eq_fwd_iff] at hB'
            obtain ⟨rfl, rfl, rfl⟩ := hB'
            obtain ⟨h₂, -⟩ := hr.atom_left rfl
            cases h₂
      · -- backward composition
        cases hB with
        | base h =>
          rcases h with h | h
          · cases h
          · cases h
            cases hA with
            | base h => cases h; exact absurd hA'.symm (slash_ne_atom _ _ _ _)
            | str =>
              rw [eq_comm, slash_eq_fwd_iff] at hA'
              obtain ⟨rfl, rfl, rfl⟩ := hA'
              obtain ⟨h₂, -⟩ := hr.atom_left rfl
              exact absurd (Cat.atom.inj h₂) hsn
    · -- AC
      cases hA with
      | base h => cases h; cases hc
      | @str Q hQ => cases hc; exact ⟨_, rfl, NotBad.acLikes hQ hB⟩
  -- Step 2: the unary closure of `S/Z₀`.
  obtain ⟨Z₀, rfl, hZ₀⟩ := key
  have hR : Raised s (PEq (S ⫽ Z₀)) P := rtg_raised s (PEq_asp (by simp [spineLength])) rfl hP₀
  cases hR with
  | base h => exact ⟨Z₀, h, hZ₀⟩
  | @str Q hQ =>
    refine ⟨_, rfl, NotBad.str hsn (Or.inr ?_)⟩
    exact hQ.fwd (fun C hC => ⟨Z₀, hC⟩)

/-- `[2,4)` (`Mary madly`): `S\(S\NP)` or some `S/Z`. -/
theorem derives24 (hsn : np ≠ s) {D : Cat Atom} (h : Derives Rf (lexAdj s np) 2 4 D) :
    D = S ⧵ (S ⧵ NP) ∨ ∃ Z, D = S ⫽ Z := by
  obtain ⟨A, B, D₀, hA, hB, hbin, hD₀⟩ := h.two rfl (by omega) (by omega)
  have hA' : Relation.ReflTransGen (Rf).unary NP A := hA
  have hB' : Relation.ReflTransGen (Rf).unary ((S ⧵ NP) ⧵ (S ⧵ NP)) B := hB
  have hA : Raised s (PNP np) A := rtg_raised s (PNP_asp np) rfl hA'
  have hB : Raised s (PMadly s np) B := rtg_raised s (PMadly_asp s np) (Or.inl rfl) hB'
  clear hA' hB'
  have key : D₀ = S ⧵ (S ⧵ NP) ∨ ∃ Z, D₀ = S ⫽ Z := by
    rcases hbin with hc | hc
    · rcases hc.inv with ⟨X, Y, rfl, rfl, rfl⟩ | ⟨X, Y, rfl, rfl, rfl⟩ |
          ⟨X, Y, A', B', s', Z', hr, rfl, hB', rfl⟩ | ⟨X, Y, A', B', s', Z', hr, hA', rfl, rfl⟩
      · -- FA
        cases hA with
        | base h => cases h
        | str hQ =>
          cases hB with
          | base h => rcases h with h | h <;> cases h
      · -- BA
        cases hB with
        | base h =>
          rcases h with h | h
          · cases h
            cases hA with
            | base h => cases h
          · cases h
            cases hA with
            | base h => cases h; exact Or.inl rfl
      · -- forward composition
        cases hA with
        | base h => cases h
        | @str Q hQ =>
          cases hB with
          | base h =>
            rcases h with rfl | rfl
            · rw [eq_comm, slash_eq_bwd_iff] at hB'
              obtain ⟨rfl, rfl, rfl⟩ := hB'
              rcases hr.inv with ⟨h₁, rfl⟩ | ⟨s'', Z'', A'', B'', hr', h₁, -⟩
              · cases h₁; exact Or.inl rfl
              · rw [eq_comm, slash_eq_bwd_iff] at h₁
                obtain ⟨rfl, rfl, rfl⟩ := h₁
                obtain ⟨h₂, -⟩ := hr'.atom_left rfl
                cases h₂
            · rw [eq_comm, slash_eq_bwd_iff] at hB'
              obtain ⟨rfl, rfl, rfl⟩ := hB'
              rcases hr.inv with ⟨h₁, rfl⟩ | ⟨s'', Z'', A'', B'', hr', h₁, -⟩
              · cases h₁
                cases hQ with
                | base h => cases h
              · rw [eq_comm, slash_eq_bwd_iff] at h₁
                obtain ⟨rfl, rfl, rfl⟩ := h₁
                obtain ⟨h₂, -⟩ := hr'.atom_left rfl
                cases h₂
          | str =>
            rw [eq_comm, slash_eq_fwd_iff] at hB'
            obtain ⟨rfl, rfl, rfl⟩ := hB'
            obtain ⟨h₂, -⟩ := hr.atom_left rfl
            cases h₂
      · -- backward composition
        cases hB with
        | base h =>
          rcases h with h | h
          · cases h
            cases hA with
            | base h => cases h; exact absurd hA'.symm (slash_ne_atom _ _ _ _)
            | str =>
              rw [eq_comm, slash_eq_fwd_iff] at hA'
              obtain ⟨rfl, rfl, rfl⟩ := hA'
              obtain ⟨h₂, -⟩ := hr.atom_left rfl
              cases h₂
          · cases h
            cases hA with
            | base h => cases h; exact absurd hA'.symm (slash_ne_atom _ _ _ _)
            | str =>
              rw [eq_comm, slash_eq_fwd_iff] at hA'
              obtain ⟨rfl, rfl, rfl⟩ := hA'
              obtain ⟨h₂, -⟩ := hr.atom_left rfl
              exact absurd (Cat.atom.inj h₂) hsn
    · cases hA with
      | base h => cases h; cases hc
      | str hQ => cases hc; exact Or.inr ⟨_, rfl⟩
  rcases key with rfl | ⟨Z, rfl⟩
  · have hR : Raised s (PEq (S ⧵ (S ⧵ NP))) D :=
      rtg_raised s (PEq_asp (by simp [spineLength])) rfl hD₀
    cases hR with
    | base h => exact Or.inl h
    | str => exact Or.inr ⟨_, rfl⟩
  · have hR : Raised s (PEq (S ⫽ Z)) D := rtg_raised s (PEq_asp (by simp [spineLength])) rfl hD₀
    cases hR with
    | base h => exact Or.inr ⟨Z, h⟩
    | str => exact Or.inr ⟨_, rfl⟩

/-! ### Binary steps out of an invariant state -/

/-- Forward composition of `S/Z` with a category whose innermost head is `S`, `S\NP`,
`S\(S\NP)` or `S/(S\Q)` needs `Z` to be that head, which `NotBad` forbids. -/
theorem fcomp_absurd {Z A' B' : Cat Atom} (hZ : NotBad s np Z) (hr : ReplaceHead Z S A' B')
    (hA' : A' = S ∨ A' = S ⧵ NP ∨ A' = S ⧵ (S ⧵ NP) ∨ ∃ Q, A' = S ⫽ (S ⧵ Q)) : False := by
  rcases hr.inv with ⟨h₁, -⟩ | ⟨s'', Z'', A'', B'', hr', h₁, -⟩
  · rcases hA' with rfl | rfl | rfl | ⟨Q, rfl⟩
    · exact hZ.ne_S h₁.symm
    · exact hZ.ne_VP h₁.symm
    · exact hZ.ne_SVP h₁.symm
    · exact hZ.ne_fwd _ h₁.symm
  · rcases hA' with rfl | rfl | rfl | ⟨Q, rfl⟩
    · exact slash_ne_atom _ _ _ _ h₁.symm
    · rw [eq_comm, slash_eq_bwd_iff] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      exact hZ.ne_S (hr'.atom_left rfl).1
    · rw [eq_comm, slash_eq_bwd_iff] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      exact hZ.ne_S (hr'.atom_left rfl).1
    · rw [eq_comm, slash_eq_fwd_iff] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      exact hZ.ne_S (hr'.atom_left rfl).1

/-- Backward composition of `S/Z` with `X\Y` needs `Y = S`, impossible for `Y ∈ {S\NP, NP}`. -/
theorem bcomp_absurd (hsn : np ≠ s) {Z A' B' Y X : Cat Atom} (hY : Y = S ⧵ NP ∨ Y = NP)
    (hr : ReplaceHead Y X A' B') {s' : Slash} {Z' : Cat Atom} (hA' : A'.slash s' Z' = S ⫽ Z) :
    False := by
  rw [slash_eq_fwd_iff] at hA'
  obtain ⟨rfl, rfl, rfl⟩ := hA'
  have := (hr.atom_left rfl).1
  rcases hY with rfl | rfl
  · cases this
  · exact hsn (Cat.atom.inj this)

/-- From `(2, S/Z)` with the word `Mary` (`[2,3)`). -/
theorem step23 {Z B C : Cat Atom} (hZ : NotBad s np Z) (hB : Raised s (PNP np) B)
    (h : (Rf).bin (S ⫽ Z) B C) : C = S ∨ ∃ Z', C = S ⫽ Z' ∧ NotBad s np Z' := by
  rcases h with hc | hc
  · rcases hc.inv with ⟨X, Y, h₁, rfl, rfl⟩ | ⟨X, Y, h₁, h₂, rfl⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, hB', rfl⟩ | ⟨X, Y, A', B', s', Z', hr, hA', h₂, rfl⟩
    · cases h₁; exact Or.inl rfl
    · cases hB with
      | base h => cases h; cases h₂
      | str => cases h₂
    · cases h₁
      exfalso
      cases hB with
      | base h => cases h; exact slash_ne_atom _ _ _ _ hB'.symm
      | str =>
        rw [eq_comm, slash_eq_fwd_iff] at hB'
        obtain ⟨rfl, rfl, rfl⟩ := hB'
        exact fcomp_absurd hZ hr (Or.inl rfl)
    · cases hB with
      | base h => cases h; cases h₂
      | str => cases h₂
  · cases hc
    exact Or.inr ⟨_, rfl, hZ.ac _⟩

/-- From `(2, S/Z)` with the constituent `Mary madly` (`[2,4)`). -/
theorem step24 (hsn : np ≠ s) {Z B C : Cat Atom} (hZ : NotBad s np Z)
    (hB : B = S ⧵ (S ⧵ NP) ∨ ∃ Z', B = S ⫽ Z') (h : (Rf).bin (S ⫽ Z) B C) :
    ∃ Z', C = S ⫽ Z' := by
  rcases h with hc | hc
  · exfalso
    rcases hc.inv with ⟨X, Y, h₁, h₂, rfl⟩ | ⟨X, Y, h₁, h₂, rfl⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, hB', rfl⟩ | ⟨X, Y, A', B', s', Z', hr, hA', h₂, rfl⟩
    · cases h₁
      rcases hB with rfl | ⟨Z', rfl⟩
      · exact hZ.ne_SVP h₂.symm
      · exact hZ.ne_fwd _ h₂.symm
    · rcases hB with rfl | ⟨Z', rfl⟩ <;> cases h₂
      cases h₁
    · cases h₁
      rcases hB with rfl | ⟨Z', rfl⟩
      · rw [eq_comm, slash_eq_bwd_iff] at hB'
        obtain ⟨rfl, rfl, rfl⟩ := hB'
        exact fcomp_absurd hZ hr (Or.inl rfl)
      · rw [eq_comm, slash_eq_fwd_iff] at hB'
        obtain ⟨rfl, rfl, rfl⟩ := hB'
        exact fcomp_absurd hZ hr (Or.inl rfl)
    · rcases hB with rfl | ⟨Z', rfl⟩ <;> cases h₂
      exact bcomp_absurd hsn (Or.inl rfl) hr hA'.symm
  · cases hc; exact ⟨_, rfl⟩

/-- From `(3, S/Z)` with the word `madly` (`[3,4)`). -/
theorem step34 (hsn : np ≠ s) {Z B C : Cat Atom} (hZ : NotBad s np Z)
    (hB : Raised s (PMadly s np) B) (h : (Rf).bin (S ⫽ Z) B C) : ∃ Z', C = S ⫽ Z' := by
  rcases h with hc | hc
  · exfalso
    rcases hc.inv with ⟨X, Y, h₁, h₂, rfl⟩ | ⟨X, Y, h₁, h₂, rfl⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, hB', rfl⟩ | ⟨X, Y, A', B', s', Z', hr, hA', h₂, rfl⟩
    · cases h₁
      cases hB with
      | base h =>
        rcases h with rfl | rfl
        · exact hZ.ne_adv h₂.symm
        · exact hZ.ne_advS h₂.symm
      | str => exact hZ.ne_fwd _ h₂.symm
    · cases hB with
      | base h => rcases h with rfl | rfl <;> cases h₂ <;> cases h₁
      | str => cases h₂
    · cases h₁
      cases hB with
      | base h =>
        rcases h with rfl | rfl
        · rw [eq_comm, slash_eq_bwd_iff] at hB'
          obtain ⟨rfl, rfl, rfl⟩ := hB'
          exact fcomp_absurd hZ hr (Or.inr (Or.inl rfl))
        · rw [eq_comm, slash_eq_bwd_iff] at hB'
          obtain ⟨rfl, rfl, rfl⟩ := hB'
          exact fcomp_absurd hZ hr (Or.inr (Or.inr (Or.inl rfl)))
      | str =>
        rw [eq_comm, slash_eq_fwd_iff] at hB'
        obtain ⟨rfl, rfl, rfl⟩ := hB'
        exact fcomp_absurd hZ hr (Or.inl rfl)
    · cases hB with
      | base h =>
        rcases h with rfl | rfl <;> cases h₂
        · exact bcomp_absurd hsn (Or.inl rfl) hr hA'.symm
        · exact bcomp_absurd hsn (Or.inr rfl) hr hA'.symm
      | str => cases h₂
  · cases hc; exact ⟨_, rfl⟩

/-- From `(3, S)` nothing combines with `madly`. -/
theorem step34_S (hsn : np ≠ s) {B C : Cat Atom} (hB : Raised s (PMadly s np) B)
    (h : (Rf).bin S B C) : False := by
  rcases h with hc | hc
  · rcases hc.inv with ⟨X, Y, h₁, -, -⟩ | ⟨X, Y, h₁, h₂, -⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, -, -⟩ | ⟨X, Y, A', B', s', Z', hr, hA', h₂, -⟩
    · cases h₁
    · cases hB with
      | base h =>
        rcases h with rfl | rfl <;> cases h₂
        · cases h₁
        · exact hsn (Cat.atom.inj h₁).symm
      | str => cases h₂
    · cases h₁
    · exact slash_ne_atom _ _ _ _ hA'.symm
  · cases hc

/-! ### The invariant is preserved -/

theorem inv_unary (hsn : np ≠ s) {j : ℕ} {C D : Cat Atom} (hC : Inv s np j C)
    (h : (Rf).unary C D) : Inv s np j D := by
  rcases h with h | h
  · rcases hC with ⟨rfl, Z, rfl, hZ⟩ | ⟨rfl, rfl | ⟨Z, rfl, hZ⟩⟩ | ⟨rfl, Z, rfl⟩
    · exact Or.inl ⟨rfl, Z, h.eq_of_atom_fwd, hZ⟩
    · exact Or.inr (Or.inl ⟨rfl, Or.inl h.eq_of_atom⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨Z, h.eq_of_atom_fwd, hZ⟩⟩)
    · exact Or.inr (Or.inr ⟨rfl, Z, h.eq_of_atom_fwd⟩)
  · cases h
    rcases hC with ⟨rfl, Z, rfl, hZ⟩ | ⟨rfl, hC⟩ | ⟨rfl, Z, rfl⟩
    · exact Or.inl ⟨rfl, _, rfl, NotBad.str hsn (Or.inr ⟨Z, rfl⟩)⟩
    · refine Or.inr (Or.inl ⟨rfl, Or.inr ⟨_, rfl, NotBad.str hsn ?_⟩⟩)
      rcases hC with rfl | ⟨Z, rfl, -⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨Z, rfl⟩
    · exact Or.inr (Or.inr ⟨rfl, _, rfl⟩)

theorem inv_bin (hsn : np ≠ s) {j k : ℕ} {A B C : Cat Atom} (hA : Inv s np j A)
    (hB : Derives Rf (lexAdj s np) j k B) (h : (Rf).bin A B C) : Inv s np k C := by
  have hjk := hB.lt
  have hk := hB.le_n
  rcases hA with ⟨rfl, Z, rfl, hZ⟩ | ⟨rfl, hA⟩ | ⟨rfl, Z, rfl⟩
  · obtain rfl | rfl : k = 3 ∨ k = 4 := by omega
    · rcases step23 hZ (derives23 hB) h with h' | ⟨Z', rfl, hZ'⟩
      · exact Or.inr (Or.inl ⟨rfl, Or.inl h'⟩)
      · exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨Z', rfl, hZ'⟩⟩)
    · obtain ⟨Z', rfl⟩ := step24 hsn hZ (derives24 hsn hB) h
      exact Or.inr (Or.inr ⟨rfl, Z', rfl⟩)
  · obtain rfl : k = 4 := by omega
    rcases hA with rfl | ⟨Z, rfl, hZ⟩
    · exact (step34_S hsn (derives34 hB) h).elim
    · obtain ⟨Z', rfl⟩ := step34 hsn hZ (derives34 hB) h
      exact Or.inr (Or.inr ⟨rfl, Z', rfl⟩)
  · omega

theorem continues_inv (hsn : np ≠ s) {P : Cat Atom} {j : ℕ} {C : Cat Atom}
    (h : Continues Rf (lexAdj s np) 2 P j C) (hP : Inv s np 2 P) : Inv s np j C := by
  induction h with
  | refl => exact hP
  | unary _ hCD ih => exact inv_unary hsn ih hCD
  | bin _ hB hABC ih => exact inv_bin hsn ih hB hABC

/-- **No category of `John likes` can be discharged by `Mary madly` to `S`.** -/
theorem lexAdj_prefix2_not_acceptable (hsn : np ≠ s) :
    ¬ ∃ P, Derives Rf (lexAdj s np) 0 2 P ∧ Continues Rf (lexAdj s np) 2 P 4 S := by
  rintro ⟨P, hP, hC⟩
  obtain ⟨Z, rfl, hZ⟩ := derives02 hsn hP
  have h4 := continues_inv hsn hC (Or.inl ⟨rfl, Z, rfl, hZ⟩)
  rcases h4 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, Z', hZ'⟩
  · omega
  · omega
  · cases hZ'

/-- **Proposition 2 is false**: `John likes Mary madly` derives `S`, but is not grammatically
acceptable under `FA/BA + Bⁿ + ASP + AC + STR`. -/
theorem lexAdj_not_grammAcceptable (hsn : np ≠ s) :
    Derives Rf (lexAdj s np) 0 4 S ∧ ¬ GrammAcceptable Rf (lexAdj s np) S :=
  ⟨(lexAdj_full s np).mono (Rules.app_le_fullStrAC s),
    fun h => lexAdj_prefix2_not_acceptable hsn (h 2 (by omega) (by omega))⟩

end Adjunct

end CCG
