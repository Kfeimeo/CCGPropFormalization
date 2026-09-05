import CCGPropFormalization.ASP
import CCGPropFormalization.Audit.AtomicTR

/-!
# Audit 4 — FA/BA + ASP and FA/BA + generalized composition + ASP

Question: with type raising switched **off**, does argument-spine permutation restore prefix
reducibility?

    prefix_reducible_app_asp      : (∃ C, Derives Rules.appAsp lex 0 n C) → PrefixReducible Rules.appAsp lex
    prefix_reducible_app_comp_asp : same for Rules.appCompAsp

**Both are false.**  ASP only re-orders the valency of *one* functor; it can never turn an
argument (an atom, or any category with ≤ 1 slot) into a functor.  So any prefix that ends in
two adjacent *arguments*, or in a functor followed by an atom it does not select, is stuck —
exactly as without type raising.

Minimal counterexamples (`n = 3`, natural CCG shapes):

* `NP  NP  (S\NP)\NP`   (two arguments before a verb-final ditransitive: "John Mary loves"):
  the prefix `NP NP` reduces to nothing.  No side condition on the atoms.
* `S/S  NP  S\NP`       ("maybe John left"): the prefix `S/S NP` reduces to nothing.

What ASP *does* buy is shown positively: `John likes Mary` is now derivable left to right
(`(S\NP)/NP ⇒ (S/NP)\NP`), and the general reassociation `A (F B) ⇒ (A F) B` holds for any
functor `F = (H\A)/B`.  Compared with unrestricted TR, ASP is non-degenerate: two atoms never
combine.  Even adding atomic-target TR on top of ASP does not help.
-/

namespace CCG

open Cat

variable {Atom : Type}

/-- In `appAsp` / `appCompAsp` the unary closure of a category is its ASP class. -/
theorem Rules.appCompAsp_unary_rtg_iff {C C' : Cat Atom} :
    Relation.ReflTransGen (Rules.appCompAsp (Atom := Atom)).unary C C' ↔ ASP C C' :=
  ASP.rtg_iff

/-! ### What ASP buys: argument-order reassociation -/

section Positive

variable {n : ℕ} {R : Rules Atom} {lex : Fin n → Cat Atom}

/-- **ASP reassociation.**  If `F = (H\A)/B` takes `B` on its right and then `A` on its left,
`A (F B)`, it can instead take `A` first and `B` second, `(A F) B`, after one ASP step.
Both the prefix `A F ⇒ H/B` and the whole `⇒ H` are derivable. -/
theorem Derives.asp_reassoc (hR : Rules.appAsp ≤ R) {i k j l : ℕ} {H A B : Cat Atom}
    (hA : Derives R lex i k A) (hF : Derives R lex k j ((H ⧵ A) ⫽ B)) (hB : Derives R lex j l B) :
    Derives R lex i j (H ⫽ B) ∧ Derives R lex i l H := by
  have hF' : Derives R lex k j ((H ⫽ B) ⧵ A) := hF.unary (hR.1 _ _ (ASP.bwd_fwd H A B))
  have h₁ : Derives R lex i j (H ⫽ B) := hA.bin hF' (hR.2 _ _ _ (App.ba (H ⫽ B) A))
  exact ⟨h₁, h₁.bin hB (hR.2 _ _ _ (App.fa H B))⟩

/-- `John likes Mary` : `NP  (S\NP)/NP  NP`. -/
def lexSVO (s np : Atom) : Fin 3 → Cat Atom :=
  ![atom np, (atom s ⧵ atom np) ⫽ atom np, atom np]

/-- `John likes ⇒ S/NP` with FA/BA + ASP only. -/
theorem lexSVO_prefix₂ (s np : Atom) : Derives Rules.appAsp (lexSVO s np) 0 2 (atom s ⫽ atom np) :=
  (Derives.asp_reassoc (Rules.le_refl _) (Derives.lex 0) (Derives.lex 1) (Derives.lex 2)).1

/-- `John likes Mary ⇒ S`, left-branching, with FA/BA + ASP only. -/
theorem lexSVO_leftSpine (s np : Atom) : LeftSpine Rules.appAsp (lexSVO s np) 0 3 (atom s) :=
  LeftSpine.bin
    (LeftSpine.bin (LeftSpine.lex 0)
      (LeftSpine.unary (LeftSpine.lex 1) (ASP.bwd_fwd (atom s) (atom np) (atom np)))
      (App.ba (atom s ⫽ atom np) (atom np)))
    (LeftSpine.lex 2) (App.fa (atom s) (atom np))

/-- `John likes Mary` is prefix reducible with FA/BA + ASP. -/
theorem lexSVO_prefixReducible (s np : Atom) : PrefixReducible Rules.appAsp (lexSVO s np) := by
  intro i h₀ h₃
  obtain rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · exact ⟨_, Derives.lex 0⟩
  · exact ⟨_, lexSVO_prefix₂ s np⟩
  · exact ⟨_, (lexSVO_leftSpine s np).toDerives⟩

/-- The syntactic collapse ASP introduces: `(X/A)/B` normally requires the string `F B A`;
with ASP the string `F A B` also derives `X`. -/
def lexVAB (x a b : Atom) : Fin 3 → Cat Atom := ![(atom x ⫽ atom a) ⫽ atom b, atom a, atom b]

theorem lexVAB_full_appAsp (x a b : Atom) : Derives Rules.appAsp (lexVAB x a b) 0 3 (atom x) :=
  Derives.bin
    (Derives.bin (Derives.unary (Derives.lex 0) (ASP.fwd_fwd (atom x) (atom a) (atom b)))
      (Derives.lex 1) (App.fa (atom x ⫽ atom b) (atom a)))
    (Derives.lex 2) (App.fa (atom x) (atom b))

/-- …whereas without ASP the prefix `(X/A)/B  A` is stuck (for `A ≠ B`). -/
theorem lexVAB_prefix_irreducible_app (x a b : Atom) (hab : a ≠ b) :
    ¬ ∃ C, Derives Rules.app (lexVAB x a b) 0 2 C := by
  rintro ⟨C, h⟩
  obtain ⟨A, B, C₀, hA, hB, hbin, -⟩ := h.two rfl (by omega) (by omega)
  have hA' : A = (atom x ⫽ atom a) ⫽ atom b := by
    clear hbin
    induction hA with
    | refl => rfl
    | tail _ h => exact h.elim
  have hB' : B = atom a := by
    clear hbin
    induction hB with
    | refl => rfl
    | tail _ h => exact h.elim
  subst hA' hB'
  cases hbin with
  | fa => exact hab rfl

end Positive

/-! ### Counterexample 1: two arguments before their functor -/

/-- `NP  NP  (S\NP)\NP` — e.g. verb-final "John Mary loves". -/
def lexSOV (s np : Atom) : Fin 3 → Cat Atom :=
  ![atom np, atom np, (atom s ⧵ atom np) ⧵ atom np]

/-- The whole sentence derives `S` by two backward applications. -/
theorem lexSOV_full (s np : Atom) : Derives Rules.appAsp (lexSOV s np) 0 3 (atom s) :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.lex 1) (Derives.lex 2) (App.ba (atom s ⧵ atom np) (atom np)))
    (App.ba (atom s) (atom np))

/-- Two atoms are never combined by any binary rule. -/
theorem Combine.not_atom_atom (a b : Atom) : ¬ ∃ C, Combine (atom a) (atom b) C := by
  rintro ⟨C, h⟩
  rcases h.inv with ⟨_, _, h, -, -⟩ | ⟨_, _, -, h, -⟩ | ⟨_, _, _, _, _, _, -, h, -, -⟩ |
      ⟨_, _, _, _, _, _, -, -, h, -⟩ <;> cases h

/-- The prefix `NP NP` derives **nothing** with FA/BA + generalized composition + ASP. -/
theorem lexSOV_prefix_irreducible (s np : Atom) :
    ¬ ∃ C, Derives Rules.appCompAsp (lexSOV s np) 0 2 C := by
  rintro ⟨C, h⟩
  obtain ⟨A, B, C₀, hA, hB, hbin, -⟩ := h.two rfl (by omega) (by omega)
  have hA : ASP (atom np) A := Rules.appCompAsp_unary_rtg_iff.mp hA
  have hB : ASP (atom np) B := Rules.appCompAsp_unary_rtg_iff.mp hB
  rw [hA.eq_of_atom, hB.eq_of_atom] at hbin
  exact Combine.not_atom_atom np np ⟨_, hbin⟩

/-- **Audit result (first goal).**  `FA/BA + ASP` does not give prefix reducibility. -/
theorem not_prefixReducible_appAsp (s np : Atom) :
    (∃ C, Derives Rules.appAsp (lexSOV s np) 0 3 C) ∧ ¬ PrefixReducible Rules.appAsp (lexSOV s np) :=
  ⟨⟨_, lexSOV_full s np⟩, fun hpr =>
    let ⟨C, hC⟩ := hpr 2 (by omega) (by omega)
    lexSOV_prefix_irreducible s np ⟨C, hC.mono Rules.appAsp_le_appCompAsp⟩⟩

/-- **Audit result (second goal).**  `FA/BA + generalized composition + ASP` does not give
prefix reducibility either. -/
theorem not_prefixReducible_appCompAsp (s np : Atom) :
    (∃ C, Derives Rules.appCompAsp (lexSOV s np) 0 3 C) ∧
      ¬ PrefixReducible Rules.appCompAsp (lexSOV s np) :=
  ⟨⟨_, (lexSOV_full s np).mono Rules.appAsp_le_appCompAsp⟩,
    fun hpr => lexSOV_prefix_irreducible s np (hpr 2 (by omega) (by omega))⟩

/-! ### Counterexample 2: a functor followed by an atom it does not select -/

/-- `S/S  NP  S\NP` — "maybe John left". -/
def lexAdv (s np : Atom) : Fin 3 → Cat Atom :=
  ![atom s ⫽ atom s, atom np, atom s ⧵ atom np]

theorem lexAdv_full (s np : Atom) : Derives Rules.appAsp (lexAdv s np) 0 3 (atom s) :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.lex 1) (Derives.lex 2) (App.ba (atom s) (atom np)))
    (App.fa (atom s) (atom s))

/-- The prefix `S/S NP` derives nothing with FA/BA + generalized composition + ASP
(`S/S` has one slot, so ASP fixes it; `NP` is an atom). -/
theorem lexAdv_prefix_irreducible (s np : Atom) (hnp : np ≠ s) :
    ¬ ∃ C, Derives Rules.appCompAsp (lexAdv s np) 0 2 C := by
  rintro ⟨C, h⟩
  obtain ⟨A, B, C₀, hA, hB, hbin, -⟩ := h.two rfl (by omega) (by omega)
  have hA : ASP (atom s ⫽ atom s) A := Rules.appCompAsp_unary_rtg_iff.mp hA
  have hB : ASP (atom np) B := Rules.appCompAsp_unary_rtg_iff.mp hB
  rw [hA.eq_of_atom_fwd, hB.eq_of_atom] at hbin
  rcases hbin.inv with ⟨X', Y', h₁, h₂, -⟩ | ⟨_, _, -, h₂, -⟩ |
      ⟨_, _, _, _, _, _, -, -, h₂, -⟩ | ⟨_, _, _, _, _, _, -, -, h₂, -⟩
  · cases h₁; cases h₂; exact hnp rfl
  · cases h₂
  · exact slash_ne_atom _ _ _ _ h₂.symm
  · cases h₂

theorem not_prefixReducible_appCompAsp' (s np : Atom) (hnp : np ≠ s) :
    (∃ C, Derives Rules.appCompAsp (lexAdv s np) 0 3 C) ∧
      ¬ PrefixReducible Rules.appCompAsp (lexAdv s np) :=
  ⟨⟨_, (lexAdv_full s np).mono Rules.appAsp_le_appCompAsp⟩,
    fun hpr => lexAdv_prefix_irreducible s np hnp (hpr 2 (by omega) (by omega))⟩

/-! ### ASP is not degenerate the way unrestricted TR is -/

/-- Contrast with `Combine.any`: under ASP there is **no** way to combine two arbitrary
categories — two atoms never combine. -/
theorem not_asp_combine_any (a : Atom) :
    ¬ ∀ A B : Cat Atom, ∃ A' B' C, ASP A A' ∧ ASP B B' ∧ Combine A' B' C := by
  intro h
  obtain ⟨A', B', C, hA, hB, hC⟩ := h (atom a) (atom a)
  rw [hA.eq_of_atom, hB.eq_of_atom] at hC
  exact Combine.not_atom_atom a a ⟨C, hC⟩

/-! ### Even ASP + atomic-target TR is not enough -/

/-- FA/BA + generalized composition + atomic-target TR + ASP. -/
abbrev Rules.atomicTRAsp : Rules Atom := Rules.atomicTR.withASP

@[simp] theorem spineLength_fwd (X A : Cat Atom) : spineLength (X ⫽ A) = spineLength X + 1 := by
  simp [spineLength]
@[simp] theorem spineLength_bwd (X A : Cat Atom) : spineLength (X ⧵ A) = spineLength X + 1 := by
  simp [spineLength]

/-- Atomic-target type raising of an atom only ever produces one-slot functors. -/
theorem TRAtom.spineLength_le_one {np : Atom} {A : Cat Atom} (h : TRAtom (atom np) A) :
    spineLength A ≤ 1 := by
  induction h with
  | refl => simp
  | tail _ h _ => obtain ⟨t, rfl | rfl⟩ := h <;> simp

/-- Hence ASP is the identity on that closure: adding ASP to atomic TR changes nothing. -/
theorem Rules.atomicTRAsp_unary_rtg {np : Atom} {A : Cat Atom}
    (h : Relation.ReflTransGen (Rules.atomicTRAsp (Atom := Atom)).unary (atom np) A) :
    TRAtom (atom np) A := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih =>
    rcases h with h | h
    · exact ih.tail h
    · rw [h.eq_of_spineLength_le_one ih.spineLength_le_one]; exact ih

theorem lexAtomic_prefix_irreducible_asp (s np : Atom) :
    ¬ ∃ C, Derives Rules.atomicTRAsp (lexAtomic s np) 0 2 C := by
  rintro ⟨C, h⟩
  obtain ⟨A, B, C₀, hA, hB, hbin, -⟩ := h.two rfl (by omega) (by omega)
  exact lexAtomic_no_combine (Rules.atomicTRAsp_unary_rtg hA) (Rules.atomicTRAsp_unary_rtg hB) hbin

/-- `NP NP (S\NP)\NP` has a full derivation but no reducible prefix `NP NP`, even with
FA/BA + generalized composition + atomic-target TR + ASP. -/
theorem not_prefixReducible_atomicTRAsp (s np : Atom) :
    (∃ C, Derives Rules.atomicTRAsp (lexAtomic s np) 0 3 C) ∧
      ¬ PrefixReducible Rules.atomicTRAsp (lexAtomic s np) :=
  ⟨⟨_, (lexAtomic_full s np).mono (Rules.le_withASP _)⟩,
    fun hpr => lexAtomic_prefix_irreducible_asp s np (hpr 2 (by omega) (by omega))⟩

end CCG
