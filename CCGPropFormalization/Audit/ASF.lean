import CCGPropFormalization.Audit.Adjunct

/-!
# Audit 7 — Argument-Spine Fusion (ASF)

    ASF-BWD :  (X\A)\B ⇒ X\C   if  App A B C        (surface order  A B [functor])
    ASF-FWD :  (X/A)/B ⇒ X/C   if  App B A C        (surface order  [functor] B A)

Implemented as an adjacent-slot rewrite on the flattened spine (`ASF`), so that fusion may
happen anywhere in the spine; the two category-level schemas of the specification are the
instances `ASF.bwd_outer` / `ASF.fwd_outer`.  Only `App` (FA/BA) is consulted, only adjacent
same-direction slots fuse, arguments stay opaque, and the rule is a one-way contraction
(`ASF.spineLength`, `ASF.irrefl`).

System studied: `FA/BA + Bⁿ + ASP + AC + STR + ASF`  (`Rules.fullStrACASF s`).

* The counterexample of Audit 6 is repaired: `John likes Mary madly` is now grammatically
  acceptable (`lexAdj_grammAcceptable_asf`), via `(S\NP)\(S\NP) ⇒ S\S`.
* **Proposition 2 is still false.**  New counterexample:

      what  apparently  Mary  likes   :   S/(S/NP)   S/S   NP   (S\NP)/NP

  The sentence derives `S` (`apparently (Mary likes) ⇒ S/NP`, then FA).  But `what` wants an
  `S/NP` and `apparently` has head `S`: composition needs the heads to match, AC can only
  capture `apparently` as an *argument*, and no rule (ASF included — every prefix category has
  one slot, and the verb's two slots point in different directions) helps.  Every category of the
  prefix `what apparently` is `S/Z` with `Z` a backward functor, while `Mary likes` only ever
  produces forward functors headed by `S` (`lexWhatApp_not_grammAcceptable`).
  The missing rule is composition *into the argument*, `X/(Y/Z)  Y/W ⇒ X/(W/Z)`
  (the `D` combinator of Hoyt & Baldridge), not slot fusion.
-/

namespace CCG

open Cat

variable {Atom : Type}

/-- **Argument-Spine Fusion.**  Two adjacent same-direction slots whose arguments combine by
FA/BA in surface order are replaced by the single result slot. -/
inductive ASF : Cat Atom → Cat Atom → Prop
  | bwd {C C' H A B D : Cat Atom} {l₁ l₂ : List (ArgSlot Atom)} :
      flattenSpine C = (H, l₁ ++ ⟨.bwd, A⟩ :: ⟨.bwd, B⟩ :: l₂) → App A B D →
      C' = rebuildSpine H (l₁ ++ ⟨.bwd, D⟩ :: l₂) → ASF C C'
  | fwd {C C' H A B D : Cat Atom} {l₁ l₂ : List (ArgSlot Atom)} :
      flattenSpine C = (H, l₁ ++ ⟨.fwd, A⟩ :: ⟨.fwd, B⟩ :: l₂) → App B A D →
      C' = rebuildSpine H (l₁ ++ ⟨.fwd, D⟩ :: l₂) → ASF C C'

namespace ASF

/-- The head is unchanged. -/
theorem head_eq {C C' : Cat Atom} (h : ASF C C') : (flattenSpine C).1 = (flattenSpine C').1 := by
  cases h with
  | @bwd H A B D l₁ l₂ h₁ _ h₂ =>
    obtain ⟨⟨a, rfl⟩, -⟩ := flattenSpine_eq_iff.mp h₁
    rw [h₂, flatten_rebuild_atom, h₁]
  | @fwd H A B D l₁ l₂ h₁ _ h₂ =>
    obtain ⟨⟨a, rfl⟩, -⟩ := flattenSpine_eq_iff.mp h₁
    rw [h₂, flatten_rebuild_atom, h₁]

/-- ASF is a contraction: it removes exactly one slot. -/
theorem spineLength {C C' : Cat Atom} (h : ASF C C') : spineLength C = spineLength C' + 1 := by
  cases h with
  | @bwd H A B D l₁ l₂ h₁ _ h₂ =>
    obtain ⟨⟨a, rfl⟩, -⟩ := flattenSpine_eq_iff.mp h₁
    unfold CCG.spineLength; rw [h₂, flatten_rebuild_atom, h₁]; simp; omega
  | @fwd H A B D l₁ l₂ h₁ _ h₂ =>
    obtain ⟨⟨a, rfl⟩, -⟩ := flattenSpine_eq_iff.mp h₁
    unfold CCG.spineLength; rw [h₂, flatten_rebuild_atom, h₁]; simp; omega

/-- Hence ASF is irreflexive — it is not an equivalence and has no inverse expansion. -/
theorem irrefl (C : Cat Atom) : ¬ ASF C C := fun h => Nat.ne_of_lt (Nat.lt_succ_self _) h.spineLength

/-- ASF needs at least two slots. -/
theorem two_le {C C' : Cat Atom} (h : ASF C C') : 2 ≤ CCG.spineLength C := by
  cases h with
  | @bwd H A B D l₁ l₂ h₁ _ _ => unfold CCG.spineLength; rw [h₁]; simp; omega
  | @fwd H A B D l₁ l₂ h₁ _ _ => unfold CCG.spineLength; rw [h₁]; simp; omega

theorem not_of_le_one {C C' : Cat Atom} (hC : CCG.spineLength C ≤ 1) : ¬ ASF C C' :=
  fun h => by have := h.two_le; omega

/-- ASF-BWD as a category-level schema: `(X\A)\B ⇒ X\C`. -/
theorem bwd_outer {X A B D : Cat Atom} (h : App A B D) : ASF ((X ⧵ A) ⧵ B) (X ⧵ D) :=
  ASF.bwd (H := (flattenSpine X).1) (l₁ := (flattenSpine X).2) (l₂ := []) (by simp) h (by simp)

/-- ASF-FWD as a category-level schema: `(X/A)/B ⇒ X/C`. -/
theorem fwd_outer {X A B D : Cat Atom} (h : App B A D) : ASF ((X ⫽ A) ⫽ B) (X ⫽ D) :=
  ASF.fwd (H := (flattenSpine X).1) (l₁ := (flattenSpine X).2) (l₂ := []) (by simp) h (by simp)

/-- The typical example: `(S\NP)\(S\NP) ⇒ S\S`. -/
theorem adverb (S NP : Cat Atom) : ASF ((S ⧵ NP) ⧵ (S ⧵ NP)) (S ⧵ S) := bwd_outer (App.ba S NP)

/-- Mixed-direction slots never fuse: a two-slot category `(a | A) |' B` with `| ≠ |'` is
ASF-inert. -/
theorem not_mixed {a : Atom} {d₁ d₂ : Dir} (hd : d₁ ≠ d₂) {A B C' : Cat Atom} :
    ¬ ASF (((atom a).slash d₁ A).slash d₂ B) C' := by
  intro h
  have h₂ : flattenSpine (((atom a).slash d₁ A).slash d₂ B) = (atom a, [⟨d₁, A⟩, ⟨d₂, B⟩]) := by
    simp
  cases h with
  | @bwd H A' B' D l₁ l₂ h₁ _ _ =>
    rw [h₂] at h₁
    obtain ⟨-, h₁⟩ := Prod.mk.inj h₁
    rcases l₁ with _ | ⟨_, l₁⟩
    · rcases l₂ with _ | ⟨_, l₂⟩
      · obtain ⟨h₃, h₄⟩ := List.cons.inj h₁
        obtain ⟨h₅, -⟩ := List.cons.inj h₄
        cases h₃; cases h₅; exact hd rfl
      · have := congrArg List.length h₁
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
    · have := congrArg List.length h₁
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega
  | @fwd H A' B' D l₁ l₂ h₁ _ _ =>
    rw [h₂] at h₁
    obtain ⟨-, h₁⟩ := Prod.mk.inj h₁
    rcases l₁ with _ | ⟨_, l₁⟩
    · rcases l₂ with _ | ⟨_, l₂⟩
      · obtain ⟨h₃, h₄⟩ := List.cons.inj h₁
        obtain ⟨h₅, -⟩ := List.cons.inj h₄
        cases h₃; cases h₅; exact hd rfl
      · have := congrArg List.length h₁
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
    · have := congrArg List.length h₁
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega

end ASF

namespace Rules

/-- FA + BA + generalized composition + ASP + AC + STR + ASF. -/
def fullStrACASF (s : Atom) : Rules Atom :=
  ⟨fun C D => ASP C D ∨ STR s C D ∨ ASF C D, fun A B C => Combine A B C ∨ AC A B C⟩

theorem fullStrAC_le_fullStrACASF (s : Atom) : fullStrAC s ≤ (fullStrACASF s : Rules Atom) :=
  ⟨fun _ _ h => h.imp id Or.inl, fun _ _ _ h => h⟩

end Rules

section ASFAudit

variable (s np : Atom)

local notation "S" => atom s
local notation "NP" => atom np
local notation "Rg" => Rules.fullStrACASF s

/-! ### The old counterexample is repaired -/

/-- `John likes Mary madly` is grammatically acceptable with ASF: `John likes ⇒ S/NP`,
`⇒ S` after `Mary`, and `madly ⇒ S\S`. -/
theorem lexAdj_grammAcceptable_asf : GrammAcceptable Rg (lexAdj s np) S := by
  intro i hi hin
  have john : Derives Rg (lexAdj s np) 0 1 (S ⫽ (S ⧵ NP)) :=
    (Derives.lex 0).unary (Or.inr (Or.inl (STR.str NP)))
  have jl : Derives Rg (lexAdj s np) 0 2 (S ⫽ NP) :=
    john.bin (Derives.lex 1) (Or.inl (Combine.fcomp₁ S (S ⧵ NP) NP))
  have jlm : Derives Rg (lexAdj s np) 0 3 S := jl.bin (Derives.lex 2) (Or.inl (Combine.fa S NP))
  have madly : Derives Rg (lexAdj s np) 3 4 (S ⧵ S) :=
    (Derives.lex 3).unary (Or.inr (Or.inr (ASF.adverb S NP)))
  have last : (Rg).bin S (S ⧵ S) S := Or.inl (Combine.ba S S)
  obtain rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · exact ⟨NP, Derives.lex 0,
      (((Continues.refl.unary (Or.inr (Or.inl (STR.str NP)))).bin (Derives.lex 1)
        (Or.inl (Combine.fcomp₁ S (S ⧵ NP) NP))).bin (Derives.lex 2)
        (Or.inl (Combine.fa S NP))).bin madly last⟩
  · exact ⟨_, jl, (Continues.refl.bin (Derives.lex 2) (Or.inl (Combine.fa S NP))).bin madly last⟩
  · exact ⟨_, jlm, Continues.refl.bin madly last⟩

/-! ### The new counterexample: `what apparently Mary likes` -/

/-- `S/(S/NP)  S/S  NP  (S\NP)/NP`. -/
def lexWhatApp : Fin 4 → Cat Atom := ![S ⫽ (S ⫽ NP), S ⫽ S, NP, (S ⧵ NP) ⫽ NP]

/-- `what (apparently (Mary likes)) ⇒ S`. -/
theorem lexWhatApp_full : Derives Rg (lexWhatApp s np) 0 4 S :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.lex 1)
      (Derives.bin ((Derives.lex 2).unary (Or.inr (Or.inl (STR.str NP)))) (Derives.lex 3)
        (Or.inl (Combine.fcomp₁ S (S ⧵ NP) NP)))
      (Or.inl (Combine.fcomp₁ S S NP)))
    (Or.inl (Combine.fa S (S ⫽ NP)))

/-- Unary closure under `ASP ∨ STR ∨ ASF` of an ASF-inert, ASP-closed base predicate. -/
theorem rtg_raised_asf {P : Cat Atom → Prop} (hP : ∀ C C', P C → ASP C C' → P C')
    (hP' : ∀ C C', P C → ¬ ASF C C') {C₀ C : Cat Atom} (h₀ : P C₀)
    (h : Relation.ReflTransGen (Rg).unary C₀ C) : Raised s P C := by
  induction h with
  | refl => exact Raised.base h₀
  | tail _ h ih =>
    rcases h with h | h | h
    · cases ih with
      | base hp => exact Raised.base (hP _ _ hp h)
      | str hQ => rw [h.eq_of_atom_fwd]; exact Raised.str hQ
    · cases h; exact Raised.str ih
    · cases ih with
      | base hp => exact (hP' _ _ hp h).elim
      | str => exact (ASF.not_of_le_one (by simp [spineLength]) h).elim

/-- What the residual `Z` of a prefix category `S/Z` looks like: a backward functor that is
neither `S\NP` nor `(S/NP)\NP` — the only backward categories the suffix could ever match. -/
structure Bwd (Z : Cat Atom) : Prop where
  bwd : ∃ Z₁ Z₂, Z = Z₁ ⧵ Z₂
  ne_VP : Z ≠ S ⧵ NP
  ne_OV : Z ≠ (S ⫽ NP) ⧵ NP

/-- Continuation-state invariant: `S/Z` with `Z` backward at `j ∈ {2,3}`, some `S/W` at `j = 4`. -/
def InvW (j : ℕ) (C : Cat Atom) : Prop :=
  ((j = 2 ∨ j = 3) ∧ ∃ Z, C = S ⫽ Z ∧ Bwd s np Z) ∨ (j = 4 ∧ ∃ W, C = S ⫽ W)

variable {s np}

/-- Base predicates for `what` and `apparently`. -/
theorem PEq_asf {C₀ : Cat Atom} (h₀ : spineLength C₀ ≤ 1) : ∀ C C', PEq C₀ C → ¬ ASF C C' := by
  rintro C C' rfl; exact ASF.not_of_le_one h₀

theorem PNP_asf : ∀ C C', PNP np C → ¬ ASF C C' := by
  rintro C C' rfl; exact ASF.not_of_le_one (by simp)

theorem PLikes_asf : ∀ C C', PLikes s np C → ¬ ASF C C' := by
  rintro C C' (rfl | rfl)
  · exact ASF.not_mixed (a := s) (d₁ := .bwd) (d₂ := .fwd) (by decide)
  · exact ASF.not_mixed (a := s) (d₁ := .fwd) (d₂ := .bwd) (by decide)

theorem Bwd.ac {Z : Cat Atom} (hZ : Bwd s np Z) (B : Cat Atom) : Bwd s np (Z ⧵ B) where
  bwd := ⟨_, _, rfl⟩
  ne_VP h := by obtain ⟨Z₁, Z₂, rfl⟩ := hZ.bwd; cases h
  ne_OV h := by obtain ⟨Z₁, Z₂, rfl⟩ := hZ.bwd; cases h

theorem Bwd.str {C : Cat Atom} (hC : ∃ W, C = S ⫽ W) : Bwd s np (S ⧵ C) where
  bwd := ⟨_, _, rfl⟩
  ne_VP h := by obtain ⟨W, rfl⟩ := hC; cases h
  ne_OV h := by cases h

/-- `Z = Y\A'` with `A'` a raised `S/S` (the AC capture of `apparently`). -/
theorem Bwd.capture {Y A' : Cat Atom} (hA : Raised s (PEq (S ⫽ S)) A') : Bwd s np (Y ⧵ A') where
  bwd := ⟨_, _, rfl⟩
  ne_VP h := by
    cases hA with
    | base hA => cases hA; cases h
    | str => cases h
  ne_OV h := by
    cases hA with
    | base hA => cases hA; cases h
    | str => cases h

/-! #### Spans -/

theorem derivesW23 {B : Cat Atom} (h : Derives Rg (lexWhatApp s np) 2 3 B) : Raised s (PNP np) B := by
  have h24 : (2 : ℕ) < 4 := by omega
  have h' : Relation.ReflTransGen (Rg).unary NP B := h.single rfl h24
  exact rtg_raised_asf s (PNP_asp np) PNP_asf rfl h'

theorem derivesW34 {B : Cat Atom} (h : Derives Rg (lexWhatApp s np) 3 4 B) :
    Raised s (PLikes s np) B := by
  have h34 : (3 : ℕ) < 4 := by omega
  have h' : Relation.ReflTransGen (Rg).unary ((S ⧵ NP) ⫽ NP) B := h.single rfl h34
  exact rtg_raised_asf s (PLikes_asp s np) PLikes_asf (Or.inl rfl) h'

/-- `[0,2)` (`what apparently`): always `S/Z` with `Z` backward. -/
theorem derivesW02 (hsn : np ≠ s) {P : Cat Atom} (h : Derives Rg (lexWhatApp s np) 0 2 P) :
    ∃ Z, P = S ⫽ Z ∧ Bwd s np Z := by
  obtain ⟨A, B, P₀, hA, hB, hbin, hP₀⟩ := h.two rfl (by omega) (by omega)
  have hA' : Relation.ReflTransGen (Rg).unary (S ⫽ (S ⫽ NP)) A := hA
  have hB' : Relation.ReflTransGen (Rg).unary (S ⫽ S) B := hB
  have hA : Raised s (PEq (S ⫽ (S ⫽ NP))) A :=
    rtg_raised_asf s (PEq_asp (by simp [spineLength])) (PEq_asf (by simp [spineLength])) rfl hA'
  have hB : Raised s (PEq (S ⫽ S)) B :=
    rtg_raised_asf s (PEq_asp (by simp [spineLength])) (PEq_asf (by simp [spineLength])) rfl hB'
  clear hA' hB'
  have key : ∃ Z, P₀ = S ⫽ Z ∧ Bwd s np Z := by
    rcases hbin with hc | hc
    · exfalso
      rcases hc.inv with ⟨X, Y, rfl, rfl, rfl⟩ | ⟨X, Y, rfl, rfl, rfl⟩ |
          ⟨X, Y, A', B', s', Z', hr, rfl, hB', rfl⟩ | ⟨X, Y, A', B', s', Z', hr, hA', rfl, rfl⟩
      · -- FA
        cases hA with
        | base h =>
          cases h
          cases hB with
          | base h => cases h; exact hsn rfl
        | str =>
          cases hB with
          | base h => cases h
      · -- BA
        cases hB with
        | base h => cases h
      · -- forward composition: the head of `apparently'` is `S`, never `Y`
        cases hB with
        | base h =>
          cases h
          rw [eq_comm, slash_eq_fwd_iff] at hB'
          obtain ⟨rfl, rfl, rfl⟩ := hB'
          obtain ⟨h₂, -⟩ := hr.atom_left rfl
          cases hA with
          | base h => cases h; cases h₂
          | str => cases h₂
        | str =>
          rw [eq_comm, slash_eq_fwd_iff] at hB'
          obtain ⟨rfl, rfl, rfl⟩ := hB'
          obtain ⟨h₂, -⟩ := hr.atom_left rfl
          cases hA with
          | base h => cases h; cases h₂
          | str => cases h₂
      · -- backward composition
        cases hB with
        | base h => cases h
    · -- AC captures `apparently'` as a backward argument
      cases hc
      cases hA with
      | base h => cases h; exact ⟨_, rfl, Bwd.capture hB⟩
      | str => exact ⟨_, rfl, Bwd.capture hB⟩
  obtain ⟨Z₀, rfl, hZ₀⟩ := key
  have hR : Raised s (PEq (S ⫽ Z₀)) P :=
    rtg_raised_asf s (PEq_asp (by simp [spineLength])) (PEq_asf (by simp [spineLength])) rfl hP₀
  cases hR with
  | base h => exact ⟨Z₀, h, hZ₀⟩
  | @str Q hQ => exact ⟨_, rfl, Bwd.str (hQ.fwd (fun C hC => ⟨Z₀, hC⟩))⟩

/-- `[2,4)` (`Mary likes`): always some `S/W`. -/
theorem derivesW24 (hsn : np ≠ s) {D : Cat Atom} (h : Derives Rg (lexWhatApp s np) 2 4 D) :
    ∃ W, D = S ⫽ W := by
  obtain ⟨A, B, D₀, hA, hB, hbin, hD₀⟩ := h.two rfl (by omega) (by omega)
  have hA' : Relation.ReflTransGen (Rg).unary NP A := hA
  have hB' : Relation.ReflTransGen (Rg).unary ((S ⧵ NP) ⫽ NP) B := hB
  have hA : Raised s (PNP np) A := rtg_raised_asf s (PNP_asp np) PNP_asf rfl hA'
  have hB : Raised s (PLikes s np) B := rtg_raised_asf s (PLikes_asp s np) PLikes_asf (Or.inl rfl) hB'
  clear hA' hB'
  have key : ∃ W, D₀ = S ⫽ W := by
    rcases hbin with hc | hc
    · rcases hc.inv with ⟨X, Y, rfl, rfl, rfl⟩ | ⟨X, Y, rfl, rfl, rfl⟩ |
          ⟨X, Y, A', B', s', Z', hr, rfl, hB', rfl⟩ | ⟨X, Y, A', B', s', Z', hr, hA', rfl, rfl⟩
      · -- FA
        cases hA with
        | base h => cases h
        | str =>
          cases hB with
          | base h => rcases h with h | h <;> cases h
      · -- BA
        cases hB with
        | base h =>
          rcases h with h | h
          · cases h
          · cases h
            cases hA with
            | base h => cases h; exact ⟨NP, rfl⟩
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
              · cases h₁; exact ⟨NP, rfl⟩
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
    · cases hA with
      | base h => cases h; cases hc
      | str => cases hc; exact ⟨_, rfl⟩
  obtain ⟨W, rfl⟩ := key
  have hR : Raised s (PEq (S ⫽ W)) D :=
    rtg_raised_asf s (PEq_asp (by simp [spineLength])) (PEq_asf (by simp [spineLength])) rfl hD₀
  cases hR with
  | base h => exact ⟨W, h⟩
  | str => exact ⟨_, rfl⟩

/-! #### Steps -/

/-- Forward composition of `S/Z` (`Z` backward) with anything headed by `S` is impossible. -/
theorem fcompW_absurd {Z A' B' : Cat Atom} (hZ : Bwd s np Z) (hr : ReplaceHead Z S A' B')
    (hA' : A' = S ∨ A' = S ⧵ NP ∨ A' = S ⫽ NP ∨ ∃ Q, A' = S ⫽ (S ⧵ Q)) : False := by
  obtain ⟨Z₁, Z₂, rfl⟩ := hZ.bwd
  rcases hr.inv with ⟨h₁, -⟩ | ⟨s'', Z'', A'', B'', hr', h₁, -⟩
  · rcases hA' with rfl | rfl | rfl | ⟨Q, rfl⟩
    · cases h₁
    · exact hZ.ne_VP h₁.symm
    · cases h₁
    · cases h₁
  · rcases hA' with rfl | rfl | rfl | ⟨Q, rfl⟩
    · exact slash_ne_atom _ _ _ _ h₁.symm
    · rw [eq_comm, slash_eq_bwd_iff] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      cases (hr'.atom_left rfl).1
    · rw [eq_comm, slash_eq_fwd_iff] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      cases (hr'.atom_left rfl).1
    · rw [eq_comm, slash_eq_fwd_iff] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      cases (hr'.atom_left rfl).1

/-- From `(2, S/Z)` with `Mary` (`[2,3)`). -/
theorem stepW23 {Z B C : Cat Atom} (hZ : Bwd s np Z) (hB : Raised s (PNP np) B)
    (h : (Rg).bin (S ⫽ Z) B C) : ∃ Z', C = S ⫽ Z' ∧ Bwd s np Z' := by
  rcases h with hc | hc
  · exfalso
    obtain ⟨Z₁, Z₂, hZ'⟩ := hZ.bwd
    rcases hc.inv with ⟨X, Y, h₁, h₂, -⟩ | ⟨X, Y, h₁, h₂, -⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, hB', -⟩ | ⟨X, Y, A', B', s', Z', hr, hA', h₂, -⟩
    · cases h₁
      cases hB with
      | base h => cases h; subst hZ'; cases h₂
      | str => subst hZ'; cases h₂
    · cases hB with
      | base h => cases h; cases h₂
      | str => cases h₂
    · cases h₁
      cases hB with
      | base h => cases h; exact slash_ne_atom _ _ _ _ hB'.symm
      | str =>
        rw [eq_comm, slash_eq_fwd_iff] at hB'
        obtain ⟨rfl, rfl, rfl⟩ := hB'
        exact fcompW_absurd hZ hr (Or.inl rfl)
    · cases hB with
      | base h => cases h; cases h₂
      | str => cases h₂
  · cases hc; exact ⟨_, rfl, hZ.ac _⟩

/-- From `(2, S/Z)` with the constituent `Mary likes` (`[2,4)`). -/
theorem stepW24 {Z B C : Cat Atom} (hZ : Bwd s np Z) (hB : ∃ W, B = S ⫽ W)
    (h : (Rg).bin (S ⫽ Z) B C) : ∃ W, C = S ⫽ W := by
  obtain ⟨W, rfl⟩ := hB
  rcases h with hc | hc
  · exfalso
    obtain ⟨Z₁, Z₂, hZ'⟩ := hZ.bwd
    rcases hc.inv with ⟨X, Y, h₁, h₂, -⟩ | ⟨X, Y, h₁, h₂, -⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, hB', -⟩ | ⟨X, Y, A', B', s', Z', hr, hA', h₂, -⟩
    · cases h₁; subst hZ'; cases h₂
    · cases h₂
    · cases h₁
      rw [eq_comm, slash_eq_fwd_iff] at hB'
      obtain ⟨rfl, rfl, rfl⟩ := hB'
      exact fcompW_absurd hZ hr (Or.inl rfl)
    · cases h₂
  · cases hc; exact ⟨_, rfl⟩

/-- From `(3, S/Z)` with `likes` (`[3,4)`). -/
theorem stepW34 (hsn : np ≠ s) {Z B C : Cat Atom} (hZ : Bwd s np Z)
    (hB : Raised s (PLikes s np) B) (h : (Rg).bin (S ⫽ Z) B C) : ∃ W, C = S ⫽ W := by
  rcases h with hc | hc
  · exfalso
    rcases hc.inv with ⟨X, Y, h₁, h₂, -⟩ | ⟨X, Y, h₁, h₂, -⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, hB', -⟩ | ⟨X, Y, A', B', s', Z', hr, hA', h₂, -⟩
    · cases h₁
      obtain ⟨Z₁, Z₂, hZ'⟩ := hZ.bwd
      cases hB with
      | base h =>
        rcases h with rfl | rfl
        · subst hZ'; cases h₂
        · exact hZ.ne_OV h₂.symm
      | str => subst hZ'; cases h₂
    · cases hB with
      | base h => rcases h with rfl | rfl <;> cases h₂; cases h₁
      | str => cases h₂
    · cases h₁
      cases hB with
      | base h =>
        rcases h with rfl | rfl
        · rw [eq_comm, slash_eq_fwd_iff] at hB'
          obtain ⟨rfl, rfl, rfl⟩ := hB'
          exact fcompW_absurd hZ hr (Or.inr (Or.inl rfl))
        · rw [eq_comm, slash_eq_bwd_iff] at hB'
          obtain ⟨rfl, rfl, rfl⟩ := hB'
          exact fcompW_absurd hZ hr (Or.inr (Or.inr (Or.inl rfl)))
      | str =>
        rw [eq_comm, slash_eq_fwd_iff] at hB'
        obtain ⟨rfl, rfl, rfl⟩ := hB'
        exact fcompW_absurd hZ hr (Or.inl rfl)
    · cases hB with
      | base h =>
        rcases h with rfl | rfl <;> cases h₂
        rw [eq_comm, slash_eq_fwd_iff] at hA'
        obtain ⟨rfl, rfl, rfl⟩ := hA'
        exact hsn (Cat.atom.inj (hr.atom_left rfl).1)
      | str => cases h₂
  · cases hc; exact ⟨_, rfl⟩

/-! #### The invariant is preserved -/

theorem invW_unary {j : ℕ} {C D : Cat Atom} (hC : InvW s np j C) (h : (Rg).unary C D) :
    InvW s np j D := by
  rcases hC with ⟨hj, Z, rfl, hZ⟩ | ⟨rfl, W, rfl⟩
  · rcases h with h | h | h
    · exact Or.inl ⟨hj, Z, h.eq_of_atom_fwd, hZ⟩
    · cases h; exact Or.inl ⟨hj, _, rfl, Bwd.str ⟨Z, rfl⟩⟩
    · exact (ASF.not_of_le_one (by simp [spineLength]) h).elim
  · rcases h with h | h | h
    · exact Or.inr ⟨rfl, W, h.eq_of_atom_fwd⟩
    · cases h; exact Or.inr ⟨rfl, _, rfl⟩
    · exact (ASF.not_of_le_one (by simp [spineLength]) h).elim

theorem invW_bin (hsn : np ≠ s) {j k : ℕ} {A B C : Cat Atom} (hA : InvW s np j A)
    (hB : Derives Rg (lexWhatApp s np) j k B) (h : (Rg).bin A B C) : InvW s np k C := by
  have hjk := hB.lt
  have hk := hB.le_n
  rcases hA with ⟨rfl | rfl, Z, rfl, hZ⟩ | ⟨rfl, W, rfl⟩
  · obtain rfl | rfl : k = 3 ∨ k = 4 := by omega
    · obtain ⟨Z', rfl, hZ'⟩ := stepW23 hZ (derivesW23 hB) h
      exact Or.inl ⟨Or.inr rfl, Z', rfl, hZ'⟩
    · obtain ⟨W, rfl⟩ := stepW24 hZ (derivesW24 hsn hB) h
      exact Or.inr ⟨rfl, W, rfl⟩
  · obtain rfl : k = 4 := by omega
    obtain ⟨W, rfl⟩ := stepW34 hsn hZ (derivesW34 hB) h
    exact Or.inr ⟨rfl, W, rfl⟩
  · omega

theorem continuesW_inv (hsn : np ≠ s) {P : Cat Atom} {j : ℕ} {C : Cat Atom}
    (h : Continues Rg (lexWhatApp s np) 2 P j C) (hP : InvW s np 2 P) : InvW s np j C := by
  induction h with
  | refl => exact hP
  | unary _ hCD ih => exact invW_unary ih hCD
  | bin _ hB hABC ih => exact invW_bin hsn ih hB hABC

/-- **No category of `what apparently` can be discharged by `Mary likes` to `S`.** -/
theorem lexWhatApp_prefix2_not_acceptable (hsn : np ≠ s) :
    ¬ ∃ P, Derives Rg (lexWhatApp s np) 0 2 P ∧ Continues Rg (lexWhatApp s np) 2 P 4 S := by
  rintro ⟨P, hP, hC⟩
  obtain ⟨Z, rfl, hZ⟩ := derivesW02 hsn hP
  have h4 := continuesW_inv hsn hC (Or.inl ⟨Or.inl rfl, Z, rfl, hZ⟩)
  rcases h4 with ⟨h, -⟩ | ⟨-, W, hW⟩
  · omega
  · cases hW

/-- **Proposition 2 is still false with ASF**: `what apparently Mary likes` derives `S` but is
not grammatically acceptable under `FA/BA + Bⁿ + ASP + AC + STR + ASF`. -/
theorem lexWhatApp_not_grammAcceptable (hsn : np ≠ s) :
    Derives Rg (lexWhatApp s np) 0 4 S ∧ ¬ GrammAcceptable Rg (lexWhatApp s np) S :=
  ⟨lexWhatApp_full s np, fun h => lexWhatApp_prefix2_not_acceptable hsn (h 2 (by omega) (by omega))⟩

end ASFAudit

end CCG
