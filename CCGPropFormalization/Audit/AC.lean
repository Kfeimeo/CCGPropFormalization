import CCGPropFormalization.Audit.ASP
import CCGPropFormalization.Audit.Strong

/-!
# Audit 5 — Argument Capture (AC)

    AC :  X/Y   A  ⇒  X/(Y\A)        (for all categories X Y A)

AC is exactly one type raising with the target fixed by the functor (`A ⇒ Y/(Y\A)`) fused with
`B¹`; see `AC.eq_tr_comp`.  Because the target is not free, AC is **not** degenerate: two atoms
still never combine.

Results:
* `FA/BA + ASP + AC` and `FA/BA + Bⁿ + ASP + AC` do **not** give prefix reducibility:
  the counterexample `NP NP (S\NP)\NP` survives, because AC needs a *forward functor* on the left
  (`not_prefixReducible_appAspAC`, `not_prefixReducible_appCompAspAC`).
* AC is powerful on the other side: a prefix that has reduced to a forward functor `X/Y` captures
  **every** continuation (`Derives.ac_capture_all`).  Hence any sentence whose first word is a
  forward functor — or, with ASP, merely *has* a forward slot — is prefix reducible
  (`prefixReducible_of_first_fwd`, `prefixReducible_of_first_has_fwd_slot`).  This is a gated form
  of the TR degeneracy: `S/S` followed by arbitrary junk is fully "derivable".
* ASP + AC dissolve the strong counterexample of Audit 2: "what John likes" now has a
  left-branching derivation of `S` (`lexWhat_leftSpine_appAspAC`).
-/

namespace CCG

open Cat

variable {Atom : Type}

/-- Argument Capture: `X/Y  A ⇒ X/(Y\A)`. -/
inductive AC : Cat Atom → Cat Atom → Cat Atom → Prop
  | ac (X Y A : Cat Atom) : AC (X ⫽ Y) A (X ⫽ (Y ⧵ A))

/-- AC = type raising with target `Y` followed by `B¹`. -/
theorem AC.eq_tr_comp (X Y A : Cat Atom) :
    TypeRaise A (Y ⫽ (Y ⧵ A)) ∧ Combine (X ⫽ Y) (Y ⫽ (Y ⧵ A)) (X ⫽ (Y ⧵ A)) :=
  ⟨TypeRaise.fwd Y A, Combine.fcomp₁ X Y (Y ⧵ A)⟩

/-- AC needs a forward functor on the left. -/
theorem AC.not_atom_left (a : Atom) (B C : Cat Atom) : ¬ AC (atom a) B C := by
  intro h; cases h

namespace Rules

/-- FA + BA + AC. -/
def appAC : Rules Atom := ⟨fun _ _ => False, fun A B C => App A B C ∨ AC A B C⟩
/-- FA + BA + ASP + AC. -/
def appAspAC : Rules Atom := ⟨ASP, fun A B C => App A B C ∨ AC A B C⟩
/-- FA + BA + generalized composition + ASP + AC. -/
def appCompAspAC : Rules Atom := ⟨ASP, fun A B C => Combine A B C ∨ AC A B C⟩

theorem appAC_le_appAspAC : (appAC : Rules Atom) ≤ appAspAC := ⟨fun _ _ h => h.elim, fun _ _ _ h => h⟩
theorem appAsp_le_appAspAC : (appAsp : Rules Atom) ≤ appAspAC := ⟨fun _ _ h => h, fun _ _ _ h => Or.inl h⟩
theorem appAspAC_le_appCompAspAC : (appAspAC : Rules Atom) ≤ appCompAspAC :=
  ⟨fun _ _ h => h, fun _ _ _ h => h.imp App.toCombine id⟩
theorem appCompAsp_le_appCompAspAC : (appCompAsp : Rules Atom) ≤ appCompAspAC :=
  ⟨fun _ _ h => h, fun _ _ _ h => Or.inl h⟩

end Rules

/-! ### The counterexample survives -/

/-- The prefix `NP NP` still derives nothing with FA/BA + Bⁿ + ASP + AC. -/
theorem lexSOV_prefix_irreducible_ac (s np : Atom) :
    ¬ ∃ C, Derives Rules.appCompAspAC (lexSOV s np) 0 2 C := by
  rintro ⟨C, h⟩
  obtain ⟨A, B, C₀, hA, hB, hbin, -⟩ := h.two rfl (by omega) (by omega)
  have hA : ASP (atom np) A := ASP.rtg_iff.mp hA
  have hB : ASP (atom np) B := ASP.rtg_iff.mp hB
  rw [hA.eq_of_atom, hB.eq_of_atom] at hbin
  rcases hbin with h | h
  · exact Combine.not_atom_atom np np ⟨_, h⟩
  · exact AC.not_atom_left np _ _ h

/-- **`FA/BA + ASP + AC` does not give prefix reducibility.** -/
theorem not_prefixReducible_appAspAC (s np : Atom) :
    (∃ C, Derives Rules.appAspAC (lexSOV s np) 0 3 C) ∧ ¬ PrefixReducible Rules.appAspAC (lexSOV s np) :=
  ⟨⟨_, (lexSOV_full s np).mono Rules.appAsp_le_appAspAC⟩, fun hpr =>
    let ⟨C, hC⟩ := hpr 2 (by omega) (by omega)
    lexSOV_prefix_irreducible_ac s np ⟨C, hC.mono Rules.appAspAC_le_appCompAspAC⟩⟩

/-- **`FA/BA + Bⁿ + ASP + AC` does not give prefix reducibility either.** -/
theorem not_prefixReducible_appCompAspAC (s np : Atom) :
    (∃ C, Derives Rules.appCompAspAC (lexSOV s np) 0 3 C) ∧
      ¬ PrefixReducible Rules.appCompAspAC (lexSOV s np) :=
  ⟨⟨_, (lexSOV_full s np).mono (Rules.le_trans Rules.appAsp_le_appAspAC Rules.appAspAC_le_appCompAspAC)⟩,
    fun hpr => lexSOV_prefix_irreducible_ac s np (hpr 2 (by omega) (by omega))⟩

/-! ### What AC buys -/

section Capture

variable {n : ℕ} {R : Rules Atom} {lex : Fin n → Cat Atom}

/-- One capture step. -/
theorem Derives.ac_capture (hR : Rules.appAC ≤ R) {i j : ℕ} {X Y A : Cat Atom}
    (h₁ : Derives R lex i j (X ⫽ Y)) (h₂ : Derives R lex j (j + 1) A) :
    Derives R lex i (j + 1) (X ⫽ (Y ⧵ A)) :=
  h₁.bin h₂ (hR.2 _ _ _ (Or.inr (AC.ac X Y A)))

/-- **A forward functor captures every continuation**: once a prefix has reduced to `X/Y`, every
longer prefix reduces to some `X/Z`. -/
theorem Derives.ac_capture_all (hR : Rules.appAC ≤ R) {i j : ℕ} {X Y : Cat Atom}
    (h : Derives R lex i j (X ⫽ Y)) : ∀ k, j ≤ k → k ≤ n → ∃ Z, Derives R lex i k (X ⫽ Z) := by
  intro k
  induction k with
  | zero => intro hjk _; have := h.lt; omega
  | succ k ih =>
    intro hjk hkn
    rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
    · exact ⟨Y, h⟩
    · obtain ⟨Z, hZ⟩ := ih (by omega) (by omega)
      exact ⟨Z ⧵ lex ⟨k, hkn⟩, hZ.ac_capture hR (Derives.lex ⟨k, hkn⟩)⟩

/-- If the first word is a forward functor, the sentence is prefix reducible with FA/BA + AC
(whatever the other words are). -/
theorem prefixReducible_of_first_fwd (hR : Rules.appAC ≤ R) (hn : 0 < n) {X Y : Cat Atom}
    (h₀ : lex ⟨0, hn⟩ = X ⫽ Y) : PrefixReducible R lex := by
  intro i hi hin
  have h₁ : Derives R lex 0 1 (lex ⟨0, hn⟩) := Derives.lex ⟨0, hn⟩
  rw [h₀] at h₁
  obtain ⟨Z, hZ⟩ := h₁.ac_capture_all hR i hi hin
  exact ⟨_, hZ⟩

/-- ASP can rotate any forward slot to the outside. -/
theorem ASP.exists_fwd_outer {C A : Cat Atom} (h : (⟨.fwd, A⟩ : ArgSlot Atom) ∈ (flattenSpine C).2) :
    ∃ X, ASP C (X ⫽ A) := by
  classical
  obtain ⟨a, ha⟩ := flattenSpine_head_isAtom C
  refine ⟨rebuildSpine (atom a) ((flattenSpine C).2.erase ⟨.fwd, A⟩), ?_⟩
  have : ASP C (rebuildSpine (atom a) ((flattenSpine C).2.erase ⟨.fwd, A⟩ ++ [⟨.fwd, A⟩])) := by
    refine ⟨by simp [ha], ?_⟩
    simp only [flatten_rebuild_atom]
    exact (List.perm_cons_erase h).trans (List.perm_append_singleton _ _).symm
  simpa using this

/-- With ASP + AC it is enough that the first word *has* a forward slot somewhere. -/
theorem prefixReducible_of_first_has_fwd_slot (hR : Rules.appAspAC ≤ R) (hn : 0 < n) {A : Cat Atom}
    (h₀ : (⟨.fwd, A⟩ : ArgSlot Atom) ∈ (flattenSpine (lex ⟨0, hn⟩)).2) : PrefixReducible R lex := by
  intro i hi hin
  obtain ⟨X, hX⟩ := ASP.exists_fwd_outer h₀
  have h₁ : Derives R lex 0 1 (X ⫽ A) := (Derives.lex ⟨0, hn⟩).unary (hR.1 _ _ hX)
  obtain ⟨Z, hZ⟩ := h₁.ac_capture_all (Rules.le_trans Rules.appAC_le_appAspAC hR) i hi hin
  exact ⟨_, hZ⟩

end Capture

/-- "maybe John left" `S/S NP S\NP` is prefix reducible with FA/BA + AC. -/
theorem lexAdv_prefixReducible_appAC (s np : Atom) : PrefixReducible Rules.appAC (lexAdv s np) :=
  prefixReducible_of_first_fwd (Rules.le_refl _) (by omega) (X := atom s) (Y := atom s) rfl

/-- **"what John likes" left to right** with FA/BA + ASP + AC — the strong counterexample of
Audit 2 dissolves: `S/(S/NP) NP ⇒ S/((S/NP)\NP)` (AC), `(S\NP)/NP ⇒ (S/NP)\NP` (ASP), then FA. -/
theorem lexWhat_leftSpine_appAspAC (s np : Atom) :
    LeftSpine Rules.appAspAC (lexWhat s np) 0 3 (atom s) :=
  LeftSpine.bin
    (LeftSpine.bin (LeftSpine.lex 0) (LeftSpine.lex 1)
      (Or.inr (AC.ac (atom s) (atom s ⫽ atom np) (atom np))))
    (LeftSpine.unary (LeftSpine.lex 2) (ASP.bwd_fwd (atom s) (atom np) (atom np)))
    (Or.inl (App.fa (atom s) ((atom s ⫽ atom np) ⧵ atom np)))

end CCG
