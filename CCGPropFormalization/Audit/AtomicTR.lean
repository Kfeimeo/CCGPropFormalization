import CCGPropFormalization.Positive

/-!
# Audit 3 — type raising must be allowed *complex* targets

`Audit/NoTR.lean` shows that type raising is indispensable; `Positive.lean` shows that
*unrestricted* type raising makes the proposition trivially true.  Is there a middle ground?
The most obvious restriction — only **atomic** targets `T` (e.g. `NP ⇒ S/(S\NP)` but never
`NP ⇒ (S\NP)/((S\NP)\NP)`) — already breaks the proposition:

  `w₁ = NP`,  `w₂ = NP`,  `w₃ = (S\NP)\NP`         (a ditransitive-like tail)

derives `S` by two backward applications, but two atomically type-raised `NP`s can never be
combined by any binary rule, so the prefix `NP NP` reduces to nothing.

So the proposition is *exactly* as strong as the type-raising targets one allows: with complex
targets it is trivially true, with atomic targets it is false.  There is no non-degenerate
reading in which it holds for all lexicons.
-/

namespace CCG

open Cat

variable {Atom : Type}

/-- Type raising restricted to **atomic** targets. -/
def Rules.atomicTR : Rules Atom :=
  ⟨fun A B => ∃ t : Atom, B = atom t ⫽ (atom t ⧵ A) ∨ B = atom t ⧵ (atom t ⫽ A), Combine⟩

theorem Rules.atomicTR_le_full : (Rules.atomicTR : Rules Atom) ≤ Rules.full := by
  refine ⟨?_, fun _ _ _ h => h⟩
  rintro A B ⟨t, rfl | rfl⟩
  · exact TypeRaise.fwd _ _
  · exact TypeRaise.bwd _ _

/-- Reflexive–transitive closure of atomic-target type raising. -/
abbrev TRAtom : Cat Atom → Cat Atom → Prop :=
  Relation.ReflTransGen (Rules.atomicTR (Atom := Atom)).unary

/-- The lexicon `[NP, NP, (S\NP)\NP]`. -/
def lexAtomic (s np : Atom) : Fin 3 → Cat Atom :=
  ![atom np, atom np, (atom s ⧵ atom np) ⧵ atom np]

/-- `NP  (NP  (S\NP)\NP) ⇒ S` by two backward applications (no type raising at all). -/
theorem lexAtomic_full (s np : Atom) : Derives Rules.atomicTR (lexAtomic s np) 0 3 (atom s) :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.lex 1) (Derives.lex 2) (Combine.ba (atom s ⧵ atom np) (atom np)))
    (Combine.ba (atom s) (atom np))

/-- An atomically type-raised `NP` never has the shape `a/B` with `B` an atomically
type-raised `NP`. -/
theorem lexAtomic_aux {np : Atom} {A : Cat Atom} (hA : TRAtom (atom np) A) :
    ∀ B, TRAtom (atom np) B → ∀ a : Atom, A ≠ atom a ⫽ B := by
  induction hA with
  | refl => intro _ _ _ h; cases h
  | tail _ hTR ih =>
    intro B hB a h
    obtain ⟨t, rfl | rfl⟩ := hTR
    · cases h
      rcases hB.cases_tail with h' | ⟨B₃, hB₃, ⟨t', h'' | h''⟩⟩
      · cases h'
      · cases h''
      · cases h''
        exact ih _ hB₃ _ rfl
    · cases h

/-- Two atomically type-raised `NP`s cannot be combined by any binary rule. -/
theorem lexAtomic_no_combine {np : Atom} {A B C : Cat Atom}
    (hA : TRAtom (atom np) A) (hB : TRAtom (atom np) B) (hC : Combine A B C) : False := by
  rcases hC.inv with ⟨X, Y, rfl, rfl, -⟩ | ⟨X, Y, rfl, rfl, -⟩ |
      ⟨X, Y, A', B', s', Z, hr, rfl, rfl, -⟩ | ⟨X, Y, A', B', s', Z, hr, rfl, rfl, -⟩
  · -- FA
    rcases hA.cases_tail with h' | ⟨A₃, hA₃, ⟨t, h | h⟩⟩
    · cases h'
    · cases h
      rcases hB.cases_tail with h' | ⟨B₃, hB₃, ⟨t', h | h⟩⟩
      · cases h'
      · cases h
      · cases h
        exact lexAtomic_aux hA₃ _ hB₃ _ rfl
    · cases h
  · -- BA
    rcases hB.cases_tail with h' | ⟨B₃, hB₃, ⟨t, h | h⟩⟩
    · cases h'
    · cases h
    · cases h
      exact lexAtomic_aux hA _ hB₃ _ rfl
  · -- forward composition
    rcases hB.cases_tail with h' | ⟨B₃, hB₃, ⟨t, h | h⟩⟩
    · exact slash_ne_atom _ _ _ _ h'
    · rw [slash_eq_fwd_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := hr.atom_left rfl
      rcases hA.cases_tail with h' | ⟨A₃, hA₃, ⟨t', h | h⟩⟩
      · cases h'
      · cases h
      · cases h
    · rw [slash_eq_bwd_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := hr.atom_left rfl
      rcases hA.cases_tail with h' | ⟨A₃, hA₃, ⟨t', h | h⟩⟩
      · cases h'
      · cases h
      · cases h
  · -- backward composition
    rcases hB.cases_tail with h' | ⟨B₃, hB₃, ⟨t, h | h⟩⟩
    · cases h'
    · cases h
    · cases h
      rcases hA.cases_tail with h' | ⟨A₃, hA₃, ⟨t', h | h⟩⟩
      · exact slash_ne_atom _ _ _ _ h'
      · rw [slash_eq_fwd_iff] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h₁, -⟩ := hr.atom_left rfl
        cases h₁
      · rw [slash_eq_bwd_iff] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h₁, -⟩ := hr.atom_left rfl
        cases h₁

/-- The prefix `NP NP` derives nothing with atomic-target type raising. -/
theorem lexAtomic_prefix_irreducible (s np : Atom) :
    ¬ ∃ C, Derives Rules.atomicTR (lexAtomic s np) 0 2 C := by
  rintro ⟨C, h⟩
  obtain ⟨A, B, C₀, hA, hB, hbin, -⟩ := h.two rfl (by omega) (by omega)
  have hA : TRAtom (atom np) A := hA
  have hB : TRAtom (atom np) B := hB
  exact lexAtomic_no_combine hA hB hbin

/-- **Counterexample theorem.**  With type raising restricted to atomic targets, a full
derivation does *not* imply prefix reducibility. -/
theorem not_prefixReducible_atomicTR (s np : Atom) :
    (∃ C, Derives Rules.atomicTR (lexAtomic s np) 0 3 C) ∧
      ¬ PrefixReducible Rules.atomicTR (lexAtomic s np) :=
  ⟨⟨_, lexAtomic_full s np⟩,
    fun hpr => lexAtomic_prefix_irreducible s np (hpr 2 (by omega) (by omega))⟩

end CCG
