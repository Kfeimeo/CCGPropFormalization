import CCGPropFormalization.Audit.AC
import CCGPropFormalization.Continuation

/-!
# Audit 6 — S-Targeted Type Raising (STR)

    STR :  X ⇒ S/(S\X)        (for every category X; `S` a fixed distinguished atom)

System studied: `FA/BA + Bⁿ + ASP + AC + STR`  (`Rules.fullStrAC s`).

**Proposition 1 (prefix reducibility): true, but trivially.**  STR turns the first word into a
forward functor `S/(S\w₁)` and AC then captures every following word (`Derives.ac_capture_all`),
so *every* sequence of categories is prefix reducible, with residual continuations
`S/(((S\w₁)\w₂)\⋯)`.  The hypothesis "there is a full derivation" is unused — this is the
degeneracy of Audit 0 again, with the TR target pinned to `S`.

**Proposition 2 (grammatical acceptability): false.**  `GrammAcceptable` asks that every prefix
have a category which the *actual* suffix discharges to `S`.  Counterexample: right adjunction

    John likes Mary madly  :  NP  (S\NP)/NP  NP  (S\NP)\(S\NP)

has an application-only derivation of `S`, but every category of the prefix `John likes` has the
form `S/Z` with a `Z` that `Mary madly` can never supply (`lexAdj_not_grammAcceptable`).
-/

namespace CCG

open Cat

variable {Atom : Type}

/-- S-targeted type raising: `X ⇒ S/(S\X)`. -/
inductive STR (s : Atom) : Cat Atom → Cat Atom → Prop
  | str (X : Cat Atom) : STR s X (atom s ⫽ (atom s ⧵ X))

theorem STR.toTypeRaise {s : Atom} {X Y : Cat Atom} (h : STR s X Y) : TypeRaise X Y := by
  cases h; exact TypeRaise.fwd _ _

namespace Rules

/-- FA + BA + generalized composition + ASP + AC + STR. -/
def fullStrAC (s : Atom) : Rules Atom :=
  ⟨fun C D => ASP C D ∨ STR s C D, fun A B C => Combine A B C ∨ AC A B C⟩

theorem appCompAspAC_le_fullStrAC (s : Atom) : (appCompAspAC : Rules Atom) ≤ fullStrAC s :=
  ⟨fun _ _ h => Or.inl h, fun _ _ _ h => h⟩

theorem app_le_fullStrAC (s : Atom) : (app : Rules Atom) ≤ fullStrAC s :=
  ⟨fun _ _ h => h.elim, fun _ _ _ h => Or.inl h.toCombine⟩

theorem appAC_le_fullStrAC (s : Atom) : (appAC : Rules Atom) ≤ fullStrAC s :=
  ⟨fun _ _ h => h.elim, fun _ _ _ h => h.imp App.toCombine id⟩

end Rules

section Positive

variable {n : ℕ} {R : Rules Atom} {lex : Fin n → Cat Atom}

/-- **Proposition 1 holds unconditionally**: with STR and AC every sequence is prefix reducible. -/
theorem prefixReducible_of_str_ac (s : Atom) (hAC : Rules.appAC ≤ R)
    (hSTR : ∀ X, R.unary X (atom s ⫽ (atom s ⧵ X))) : PrefixReducible R lex := by
  intro i hi hin
  have hn : 0 < n := lt_of_lt_of_le hi hin
  have h₁ : Derives R lex 0 1 (atom s ⫽ (atom s ⧵ lex ⟨0, hn⟩)) :=
    (Derives.lex ⟨0, hn⟩).unary (hSTR _)
  obtain ⟨Z, hZ⟩ := h₁.ac_capture_all hAC i hi hin
  exact ⟨_, hZ⟩

theorem prefixReducible_fullStrAC (s : Atom) (lex : Fin n → Cat Atom) :
    PrefixReducible (Rules.fullStrAC s) lex :=
  prefixReducible_of_str_ac s (Rules.appAC_le_fullStrAC s) (fun X => Or.inr (STR.str X))

/-- …and the hypothesis of Proposition 1 is itself always satisfied. -/
theorem exists_full_derivation_fullStrAC (s : Atom) (lex : Fin n → Cat Atom) (hn : 0 < n) :
    ∃ C, Derives (Rules.fullStrAC s) lex 0 n C :=
  prefixReducible_fullStrAC s lex n hn le_rfl

end Positive

/-! ### The example of the question: `NP NP (S\NP)\NP` is grammatically acceptable -/

section Examples

variable (s np : Atom)

local notation "S" => atom s
local notation "NP" => atom np

/-- `NP ⇒ S/(S\NP)`, AC captures the second `NP`, FA with the verb. -/
theorem lexSOV_grammAcceptable : GrammAcceptable (Rules.fullStrAC s) (lexSOV s np) S := by
  intro i hi hin
  have str₀ : Derives (Rules.fullStrAC s) (lexSOV s np) 0 1 (S ⫽ (S ⧵ NP)) :=
    (Derives.lex 0).unary (Or.inr (STR.str NP))
  have cap : Derives (Rules.fullStrAC s) (lexSOV s np) 0 2 (S ⫽ ((S ⧵ NP) ⧵ NP)) :=
    str₀.bin (Derives.lex 1) (Or.inr (AC.ac S (S ⧵ NP) NP))
  have fa : (Rules.fullStrAC s).bin (S ⫽ ((S ⧵ NP) ⧵ NP)) ((S ⧵ NP) ⧵ NP) S :=
    Or.inl (Combine.fa S ((S ⧵ NP) ⧵ NP))
  obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
  · refine ⟨NP, Derives.lex 0, ?_⟩
    exact ((Continues.refl.unary (Or.inr (STR.str NP))).bin (Derives.lex 1)
      (Or.inr (AC.ac S (S ⧵ NP) NP))).bin (Derives.lex 2) fa
  · exact ⟨_, cap, Continues.refl.bin (Derives.lex 2) fa⟩

/-- "what John likes" is grammatically acceptable too (AC + ASP, Audit 5). -/
theorem lexWhat_grammAcceptable : GrammAcceptable (Rules.fullStrAC s) (lexWhat s np) S := by
  intro i hi hin
  have cap : Derives (Rules.fullStrAC s) (lexWhat s np) 0 2 (S ⫽ ((S ⫽ NP) ⧵ NP)) :=
    (Derives.lex 0).bin (Derives.lex 1) (Or.inr (AC.ac S (S ⫽ NP) NP))
  have verb : Derives (Rules.fullStrAC s) (lexWhat s np) 2 3 ((S ⫽ NP) ⧵ NP) :=
    (Derives.lex 2).unary (Or.inl (ASP.bwd_fwd S NP NP))
  have fa : (Rules.fullStrAC s).bin (S ⫽ ((S ⫽ NP) ⧵ NP)) ((S ⫽ NP) ⧵ NP) S :=
    Or.inl (Combine.fa S ((S ⫽ NP) ⧵ NP))
  obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
  · exact ⟨_, Derives.lex 0,
      (Continues.refl.bin (Derives.lex 1) (Or.inr (AC.ac S (S ⫽ NP) NP))).bin verb fa⟩
  · exact ⟨_, cap, Continues.refl.bin verb fa⟩

end Examples

end CCG
