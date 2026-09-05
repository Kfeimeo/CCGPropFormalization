import CCGPropFormalization.Audit.NoTR
import CCGPropFormalization.Audit.AtomicTR
import CCGPropFormalization.Audit.Strong
import CCGPropFormalization.Audit.ASP
import CCGPropFormalization.Audit.AC

/-!
# Small `S/NP` examples

Concrete derivations exercising FA, BA, type raising and generalized composition, plus
instances of the main theorems and counterexamples on a concrete atom type.
-/

namespace CCG.Examples

open CCG Cat

/-- Atomic categories for the examples. -/
inductive At
  | s
  | np
  | n
  deriving DecidableEq, Repr

/-- `S` -/
abbrev S : Cat At := atom .s
/-- `NP` -/
abbrev NP : Cat At := atom .np
/-- `N` -/
abbrev N : Cat At := atom .n

/-- `John likes Mary` : `NP  (S\NP)/NP  NP`. -/
def johnLikesMary : Fin 3 → Cat At := ![NP, (S ⧵ NP) ⫽ NP, NP]

/-- FA: `likes Mary ⇒ S\NP`. -/
example : Derives Rules.full johnLikesMary 1 3 (S ⧵ NP) :=
  Derives.bin (Derives.lex 1) (Derives.lex 2) (Combine.fa (S ⧵ NP) NP)

/-- BA, right-branching: `John (likes Mary) ⇒ S`. -/
example : Derives Rules.full johnLikesMary 0 3 S :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.lex 1) (Derives.lex 2) (Combine.fa (S ⧵ NP) NP))
    (Combine.ba S NP)

/-- TR + `B¹`: `(John likes) ⇒ S/NP`. -/
example : Derives Rules.full johnLikesMary 0 2 (S ⫽ NP) :=
  Derives.bin (Derives.unary (Derives.lex 0) (TypeRaise.fwd S NP)) (Derives.lex 1)
    (Combine.fcomp₁ S (S ⧵ NP) NP)

/-- Left-branching derivation `((John likes) Mary) ⇒ S`. -/
example : LeftSpine Rules.full johnLikesMary 0 3 S :=
  LeftSpine.bin
    (LeftSpine.bin (LeftSpine.unary (LeftSpine.lex 0) (TypeRaise.fwd S NP)) (LeftSpine.lex 1)
      (Combine.fcomp₁ S (S ⧵ NP) NP))
    (LeftSpine.lex 2) (Combine.fa S NP)

/-- Type raising in both directions. -/
example : TypeRaise NP (S ⫽ (S ⧵ NP)) := TypeRaise.fwd S NP
example : TypeRaise NP (S ⧵ (S ⫽ NP)) := TypeRaise.bwd S NP

/-- Generalized composition `B²`: `(S\NP)/(S\NP)  ((S\NP)/NP)/NP ⇒ ((S\NP)/NP)/NP`
("might give"). -/
example : Combine ((S ⧵ NP) ⫽ (S ⧵ NP)) (((S ⧵ NP) ⫽ NP) ⫽ NP) (((S ⧵ NP) ⫽ NP) ⫽ NP) :=
  Combine.fcomp .fwd NP (ReplaceHead.step .fwd NP ReplaceHead.refl)

/-- `B³` with a mixed spine: `S/NP  ((NP/N)\N)/N ⇒ ((S/N)\N)/N`. -/
example : Combine (S ⫽ NP) (((NP ⫽ N) ⧵ N) ⫽ N) (((S ⫽ N) ⧵ N) ⫽ N) :=
  Combine.fcomp .fwd N (ReplaceHead.step .bwd N (ReplaceHead.step .fwd N ReplaceHead.refl))

/-- The same spine, spelled out as a list. -/
example : ReplaceHead NP S (((NP ⫽ N) ⧵ N) ⫽ N) (((S ⫽ N) ⧵ N) ⫽ N) := by
  rw [ReplaceHead.iff_spine]
  exact ⟨[(.fwd, N), (.bwd, N), (.fwd, N)], rfl, rfl⟩

/-- Crossed `B¹ₓ`: `S/NP  NP\N ⇒ S\N`. -/
example : Combine (S ⫽ NP) (NP ⧵ N) (S ⧵ N) := Combine.fcomp .bwd N ReplaceHead.refl

/-- Backward composition: `NP\N  S\NP ⇒ S\N`. -/
example : Combine (NP ⧵ N) (S ⧵ NP) (S ⧵ N) := Combine.bcomp .bwd N ReplaceHead.refl

/-! ## Instances of the main results -/

/-- The target theorem on `John likes Mary`. -/
example : PrefixReducible Rules.full johnLikesMary :=
  prefix_reducible_of_full_derivation _ ⟨S, Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.lex 1) (Derives.lex 2) (Combine.fa (S ⧵ NP) NP)) (Combine.ba S NP)⟩

/-- …but it also holds for the word salad `NP NP NP`, which even has a "full derivation". -/
example : PrefixReducible Rules.full (![NP, NP, NP] : Fin 3 → Cat At) := prefixReducible_full _
example : ∃ C, Derives Rules.full (![NP, NP, NP] : Fin 3 → Cat At) 0 3 C :=
  exists_full_derivation _ (by omega)

/-- The generic two-word combination used by the positive proof, on `NP NP`:
`NP ⇒ NP/(NP\NP)`, `NP ⇒ (NP\NP)/((NP\NP)\NP)`, then `B¹`. -/
example : Derives Rules.full (![NP, NP, NP] : Fin 3 → Cat At) 0 2 (NP ⫽ ((NP ⧵ NP) ⧵ NP)) :=
  Derives.bin (Derives.unary (Derives.lex 0) (TypeRaise.fwd NP NP))
    (Derives.unary (Derives.lex 1) (TypeRaise.fwd (NP ⧵ NP) NP))
    (Combine.fcomp₁ NP (NP ⧵ NP) ((NP ⧵ NP) ⧵ NP))

/-- Audit 1 on concrete atoms: `S/NP  N  NP\N` (no type raising). -/
example : (∃ C, Derives Rules.noTR (lexNoTR At.s At.np At.n) 0 3 C) ∧
    ¬ PrefixReducible Rules.noTR (lexNoTR At.s At.np At.n) :=
  not_prefixReducible_noTR At.s At.np At.n (by decide)

/-- Audit 3 on concrete atoms: `NP NP (S\NP)\NP` with atomic-target type raising. -/
example : (∃ C, Derives Rules.atomicTR (lexAtomic At.s At.np) 0 3 C) ∧
    ¬ PrefixReducible Rules.atomicTR (lexAtomic At.s At.np) :=
  not_prefixReducible_atomicTR At.s At.np

/-- Audit 2 on concrete atoms: `what John likes` derives `S` but not incrementally. -/
example : Derives Rules.full (lexWhat At.s At.np) 0 3 S ∧
    ¬ LeftSpine Rules.full (lexWhat At.s At.np) 0 3 S :=
  not_strong_left_spine_normalization At.s At.np

example : ¬ StrongPrefixReducible Rules.full (lexWhat At.s At.np) S :=
  lexWhat_not_strongPrefixReducible At.s At.np

/-! ## Argument-spine permutation (ASP) -/

/-- Flattening follows the result spine only. -/
example : flattenSpine (((S ⧵ NP) ⫽ NP) ⫽ N) = (S, [⟨.bwd, NP⟩, ⟨.fwd, NP⟩, ⟨.fwd, N⟩]) := rfl
/-- …and never enters an argument. -/
example : flattenSpine (S ⧵ (NP ⫽ N)) = (S, [⟨.bwd, NP ⫽ N⟩]) := rfl
example : rebuildSpine S [⟨.bwd, NP⟩, ⟨.fwd, NP⟩] = (S ⧵ NP) ⫽ NP := rfl

/-- `(S\NP)/NP ⇒ (S/NP)\NP` (decided by computation). -/
example : ASP ((S ⧵ NP) ⫽ NP) ((S ⫽ NP) ⧵ NP) := by decide
/-- `((S\NP)/NP)/N ⇒ ((S/NP)\NP)/N`. -/
example : ASP (((S ⧵ NP) ⫽ NP) ⫽ N) (((S ⫽ NP) ⧵ NP) ⫽ N) := by decide
/-- `(S/NP)/N ⇒ (S/N)/NP`. -/
example : ASP ((S ⫽ NP) ⫽ N) ((S ⫽ N) ⫽ NP) := by decide
/-- Slots move as a whole: swapping only the slashes is **not** ASP. -/
example : ¬ ASP ((S ⧵ NP) ⫽ N) ((S ⫽ NP) ⧵ N) := by decide
/-- Arguments are opaque: nothing inside `NP/N` can be touched. -/
example : ¬ ASP (S ⧵ (NP ⫽ N)) (S ⧵ (N ⫽ NP)) := by decide
example : ¬ ASP (S ⧵ (NP ⫽ N)) ((S ⫽ N) ⧵ NP) := by decide
/-- The head is invariant. -/
example : ¬ ASP (S ⫽ NP) (N ⫽ NP) := by decide

/-- `John likes Mary` left to right with FA/BA + ASP only. -/
example : LeftSpine Rules.appAsp (lexSVO At.s At.np) 0 3 S := lexSVO_leftSpine At.s At.np
example : PrefixReducible Rules.appAsp (lexSVO At.s At.np) := lexSVO_prefixReducible At.s At.np

/-- Audit 4 on concrete atoms. -/
example : (∃ C, Derives Rules.appAsp (lexSOV At.s At.np) 0 3 C) ∧
    ¬ PrefixReducible Rules.appAsp (lexSOV At.s At.np) :=
  not_prefixReducible_appAsp At.s At.np
example : (∃ C, Derives Rules.appCompAsp (lexAdv At.s At.np) 0 3 C) ∧
    ¬ PrefixReducible Rules.appCompAsp (lexAdv At.s At.np) :=
  not_prefixReducible_appCompAsp' At.s At.np (by decide)

/-! ## Argument capture (AC) -/

/-- Audit 5 on concrete atoms: `NP NP (S\NP)\NP` is still a counterexample with AC. -/
example : (∃ C, Derives Rules.appCompAspAC (lexSOV At.s At.np) 0 3 C) ∧
    ¬ PrefixReducible Rules.appCompAspAC (lexSOV At.s At.np) :=
  not_prefixReducible_appCompAspAC At.s At.np
/-- …while `S/S NP S\NP` and `what John likes` become incremental. -/
example : PrefixReducible Rules.appAC (lexAdv At.s At.np) := lexAdv_prefixReducible_appAC At.s At.np
example : LeftSpine Rules.appAspAC (lexWhat At.s At.np) 0 3 S := lexWhat_leftSpine_appAspAC At.s At.np
/-- The gated degeneracy of AC: `S/S` followed by junk is "fully derivable". -/
example : ∃ C, Derives Rules.appAC (![S ⫽ S, N, NP, N] : Fin 4 → Cat At) 0 4 C :=
  prefixReducible_of_first_fwd (Rules.le_refl _) (by omega) (X := S) (Y := S) rfl 4 (by omega) le_rfl

end CCG.Examples
