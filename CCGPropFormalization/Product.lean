import CCGPropFormalization.ASP
import CCGPropFormalization.Derivation

/-!
# Product states and Spine Application

The minimal system of this round:

    FA/BA + generalized composition + Product (*) + Spine Application (SA)

* **Product.**  `A₁ * ⋯ * Aₖ` is represented canonically by the list `[A₁, …, Aₖ]`.
  Associativity is definitional (`List.append_assoc`); there is no commutativity.
  Product introduction is list concatenation (`RunFrom.shift`), and *context-closed reduction*
  `L * (A * B) * R ⇒ L * C * R` is `Reduce`.  Products never occur inside a slash — they are
  parser states, not lexical categories — so `Cat` itself is unchanged.
* **Spine Application.**  `SA A F C` deletes one slot of `F`'s outer argument spine that matches
  the adjacent category `A`, keeping the order of the remaining slots (`SA.left`, `SA.right`).
  FA/BA are the instances where the slot is outermost (`SA.of_fa`, `SA.of_ba`); every SA step is
  one ASP rotation followed by one application (`SA.asp_app`).
* **Runs.**  `RunFrom red lex i st j st'` : starting after `i` words in state `st`, shift the
  words `i, …, j-1` and apply `red`-reductions in any interleaving, ending in `st'`.
  `Run red lex n [S]` is a strict left-to-right product run ending in `S`.
  `TopReduce` reduces only the two most recent constituents (a plain parser stack);
  `Reduce` reduces anywhere (the ordered buffer of the specification).
* **Eager runs.**  `EagerRun` additionally requires the state after each shift to be reduced
  to a normal form (`Irreducible`).  This is where the audit becomes non-trivial.
-/

namespace CCG

open Cat

variable {Atom : Type}

/-! ### Spine Application -/

/-- Spine Application: discharge one matching slot anywhere in the outer argument spine. -/
inductive SA : Cat Atom → Cat Atom → Cat Atom → Prop
  /-- `A, X[Γ,(\,A),Δ] ⇒ X[Γ,Δ]` -/
  | left {A F H : Cat Atom} {Γ Δ : List (ArgSlot Atom)} :
      flattenSpine F = (H, Γ ++ ⟨.bwd, A⟩ :: Δ) → SA A F (rebuildSpine H (Γ ++ Δ))
  /-- `X[Γ,(/,A),Δ], A ⇒ X[Γ,Δ]` -/
  | right {A F H : Cat Atom} {Γ Δ : List (ArgSlot Atom)} :
      flattenSpine F = (H, Γ ++ ⟨.fwd, A⟩ :: Δ) → SA F A (rebuildSpine H (Γ ++ Δ))

namespace SA

/-- Inversion principle. -/
theorem inv {A B C : Cat Atom} (h : SA A B C) :
    (∃ H Γ Δ, flattenSpine B = (H, Γ ++ ⟨.bwd, A⟩ :: Δ) ∧ C = rebuildSpine H (Γ ++ Δ)) ∨
    (∃ H Γ Δ, flattenSpine A = (H, Γ ++ ⟨.fwd, B⟩ :: Δ) ∧ C = rebuildSpine H (Γ ++ Δ)) := by
  cases h with
  | left h => exact Or.inl ⟨_, _, _, h, rfl⟩
  | right h => exact Or.inr ⟨_, _, _, h, rfl⟩

/-- FA is SA on the outermost forward slot. -/
theorem of_fa (X Y : Cat Atom) : SA (X ⫽ Y) Y X := by
  have h := SA.right (A := Y) (F := X ⫽ Y) (H := (flattenSpine X).1) (Γ := (flattenSpine X).2)
    (Δ := []) (by simp)
  simpa using h

/-- BA is SA on the outermost backward slot. -/
theorem of_ba (X Y : Cat Atom) : SA Y (X ⧵ Y) X := by
  have h := SA.left (A := Y) (F := X ⧵ Y) (H := (flattenSpine X).1) (Γ := (flattenSpine X).2)
    (Δ := []) (by simp)
  simpa using h

theorem of_app {A B C : Cat Atom} (h : App A B C) : SA A B C := by
  cases h with
  | fa => exact of_fa _ _
  | ba => exact of_ba _ _

/-- **SA ⊆ ASP ; App**: every SA step is one argument-spine rotation followed by one ordinary
application.  So SA is at most as strong as unrestricted ASP. -/
theorem asp_app {A B C : Cat Atom} (h : SA A B C) :
    (∃ F', ASP B F' ∧ App A F' C) ∨ (∃ F', ASP A F' ∧ App F' B C) := by
  rcases h.inv with ⟨H, Γ, Δ, h₁, rfl⟩ | ⟨H, Γ, Δ, h₁, rfl⟩
  · obtain ⟨⟨a, rfl⟩, -⟩ := flattenSpine_eq_iff.mp h₁
    refine Or.inl ⟨rebuildSpine (atom a) (Γ ++ Δ) ⧵ A, ⟨?_, ?_⟩, App.ba _ _⟩
    · simp [h₁]
    · simp only [h₁, flattenSpine_bwd, flatten_rebuild_atom]
      exact List.perm_middle.trans (List.perm_append_singleton _ _).symm
  · obtain ⟨⟨a, rfl⟩, -⟩ := flattenSpine_eq_iff.mp h₁
    refine Or.inr ⟨rebuildSpine (atom a) (Γ ++ Δ) ⫽ B, ⟨?_, ?_⟩, App.fa _ _⟩
    · simp [h₁]
    · simp only [h₁, flattenSpine_fwd, flatten_rebuild_atom]
      exact List.perm_middle.trans (List.perm_append_singleton _ _).symm

end SA

/-- Binary rules of the minimal system: FA/BA + generalized composition + SA. -/
def ProdBin (A B C : Cat Atom) : Prop := Combine A B C ∨ SA A B C
/-- Without generalized composition: FA/BA + SA (= SA, since FA/BA ⊆ SA). -/
def AppSA (A B C : Cat Atom) : Prop := App A B C ∨ SA A B C

theorem AppSA.prodBin {A B C : Cat Atom} (h : AppSA A B C) : ProdBin A B C :=
  h.imp App.toCombine id

theorem Rules.app_le_noTR : (Rules.app : Rules Atom) ≤ Rules.noTR :=
  ⟨fun _ _ h => h.elim, fun _ _ _ h => h.toCombine⟩

/-! ### Buffers, reductions, runs -/

/-- A product state `A₁ * ⋯ * Aₖ`. -/
abbrev Buffer (Atom : Type) := List (Cat Atom)

/-- Context-closed reduction: `L * (A * B) * R ⇒ L * C * R`. -/
def Reduce (bin : Cat Atom → Cat Atom → Cat Atom → Prop) (st st' : Buffer Atom) : Prop :=
  ∃ L A B C R, st = L ++ A :: B :: R ∧ bin A B C ∧ st' = L ++ C :: R

/-- Stack discipline: reduce only the two most recent constituents. -/
def TopReduce (bin : Cat Atom → Cat Atom → Cat Atom → Prop) (st st' : Buffer Atom) : Prop :=
  ∃ L A B C, st = L ++ [A, B] ∧ bin A B C ∧ st' = L ++ [C]

theorem TopReduce.reduce {bin} {st st' : Buffer Atom} (h : TopReduce bin st st') : Reduce bin st st' :=
  let ⟨L, A, B, C, h₁, h₂, h₃⟩ := h
  ⟨L, A, B, C, [], h₁, h₂, h₃⟩

theorem Reduce.mono {bin bin' : Cat Atom → Cat Atom → Cat Atom → Prop}
    (h : ∀ A B C, bin A B C → bin' A B C) {st st' : Buffer Atom} (hr : Reduce bin st st') :
    Reduce bin' st st' :=
  let ⟨L, A, B, C, R, h₁, h₂, h₃⟩ := hr
  ⟨L, A, B, C, R, h₁, h _ _ _ h₂, h₃⟩

variable {n : ℕ}

/-- A strict left-to-right run: from state `st` after `i` words, shift words and reduce (with
`red`) in any interleaving, reaching state `st'` after `j` words. -/
inductive RunFrom (red : Buffer Atom → Buffer Atom → Prop) (lex : Fin n → Cat Atom) (i : ℕ)
    (st : Buffer Atom) : ℕ → Buffer Atom → Prop
  | refl : RunFrom red lex i st i st
  /-- Product introduction: read the next word. -/
  | shift {j : ℕ} {st' : Buffer Atom} : RunFrom red lex i st j st' → (hj : j < n) →
      RunFrom red lex i st (j + 1) (st' ++ [lex ⟨j, hj⟩])
  /-- A local reduction inside the current state. -/
  | reduce {j : ℕ} {st' st'' : Buffer Atom} : RunFrom red lex i st j st' → red st' st'' →
      RunFrom red lex i st j st''

/-- A run from the empty state. -/
abbrev Run (red : Buffer Atom → Buffer Atom → Prop) (lex : Fin n → Cat Atom) (i : ℕ)
    (st : Buffer Atom) : Prop :=
  RunFrom red lex 0 [] i st

namespace RunFrom

variable {red : Buffer Atom → Buffer Atom → Prop} {lex : Fin n → Cat Atom}

theorem trans {i j k : ℕ} {st st' st'' : Buffer Atom} (h₁ : RunFrom red lex i st j st')
    (h₂ : RunFrom red lex j st' k st'') : RunFrom red lex i st k st'' := by
  induction h₂ with
  | refl => exact h₁
  | shift _ hj ih => exact ih.shift hj
  | reduce _ hr ih => exact ih.reduce hr

theorem mono {red' : Buffer Atom → Buffer Atom → Prop} (h : ∀ st st', red st st' → red' st st')
    {i j : ℕ} {st st' : Buffer Atom} (hr : RunFrom red lex i st j st') :
    RunFrom red' lex i st j st' := by
  induction hr with
  | refl => exact refl
  | shift _ hj ih => exact ih.shift hj
  | reduce _ hr ih => exact ih.reduce (h _ _ hr)

theorem ofRTG {j : ℕ} {st st' : Buffer Atom} (h : Relation.ReflTransGen red st st') :
    RunFrom red lex j st j st' := by
  induction h with
  | refl => exact refl
  | tail _ hr ih => exact ih.reduce hr

theorem le {i j : ℕ} {st st' : Buffer Atom} (h : RunFrom red lex i st j st') : i ≤ j := by
  induction h with
  | refl => exact le_rfl
  | shift _ _ ih => exact Nat.le_succ_of_le ih
  | reduce _ _ ih => exact ih

end RunFrom

/-! ### Every derivation is a (stack) run — the simulation theorem -/

/-- **Simulation.**  A derivation of `C` over `[i, j)` is a run that pushes `C` onto any stack,
using only top-of-stack reductions and no unary rules. -/
theorem Derives.runFrom {R : Rules Atom} {lex : Fin n → Cat Atom}
    (hu : ∀ C D : Cat Atom, ¬ R.unary C D) {i j : ℕ} {C : Cat Atom} (h : Derives R lex i j C)
    (st : Buffer Atom) : RunFrom (TopReduce R.bin) lex i st j (st ++ [C]) := by
  induction h generalizing st with
  | lex i₀ => exact RunFrom.refl.shift i₀.isLt
  | unary _ hCD => exact (hu _ _ hCD).elim
  | bin _ _ hABC ih₁ ih₂ =>
    refine ((ih₁ st).trans (ih₂ (st ++ [_]))).reduce ⟨st, _, _, _, by simp, hABC, rfl⟩

/-! ### The words of a span, and reductions inside a context -/

/-- `Words lex i j l` : `l` is the list of lexical categories of the words `i, …, j-1`. -/
inductive Words (lex : Fin n → Cat Atom) (i : ℕ) : ℕ → Buffer Atom → Prop
  | refl : Words lex i i []
  | snoc {j : ℕ} {l : Buffer Atom} : Words lex i j l → (hj : j < n) →
      Words lex i (j + 1) (l ++ [lex ⟨j, hj⟩])

namespace Words

variable {lex : Fin n → Cat Atom}

theorem le {i j : ℕ} {l : Buffer Atom} (h : Words lex i j l) : i ≤ j := by
  induction h with
  | refl => exact le_rfl
  | snoc _ _ ih => exact Nat.le_succ_of_le ih

theorem length {i j : ℕ} {l : Buffer Atom} (h : Words lex i j l) : l.length = j - i := by
  induction h with
  | refl => simp
  | snoc h _ ih => have := h.le; simp [ih]; omega

theorem exists_of_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : ∃ l, Words lex i j l := by
  induction j with
  | zero => exact ⟨[], (Nat.le_zero.mp hij) ▸ Words.refl⟩
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact ⟨[], Words.refl⟩
    · obtain ⟨l, hl⟩ := ih (by omega) (by omega)
      exact ⟨_, hl.snoc (by omega)⟩

theorem append {i k j : ℕ} {l₁ l₂ : Buffer Atom} (h₁ : Words lex i k l₁) (h₂ : Words lex k j l₂) :
    Words lex i j (l₁ ++ l₂) := by
  induction h₂ with
  | refl => simpa using h₁
  | snoc _ hj ih => simpa [← List.append_assoc] using ih.snoc hj

theorem eq_nil {i : ℕ} {l : Buffer Atom} (h : Words lex i i l) : l = [] := by
  cases h with
  | refl => rfl
  | snoc h _ => have := h.le; omega

theorem succ_inv {i j : ℕ} {l : Buffer Atom} (h : Words lex i j l) (hj : j = i + 1) :
    ∃ hi : i < n, l = [lex ⟨i, hi⟩] := by
  cases h with
  | refl => omega
  | @snoc j l h hj' =>
    obtain rfl : j = i := by omega
    exact ⟨hj', by rw [h.eq_nil]; rfl⟩

theorem split {i j : ℕ} {l : Buffer Atom} (h : Words lex i j l) (k : ℕ) (hik : i ≤ k) (hkj : k ≤ j) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ Words lex i k l₁ ∧ Words lex k j l₂ := by
  induction h with
  | refl => exact ⟨[], [], rfl, (by omega : i = k) ▸ Words.refl, (by omega : i = k) ▸ Words.refl⟩
  | @snoc j l h hj ih =>
    rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
    · exact ⟨_, [], by simp, h.snoc hj, Words.refl⟩
    · obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := ih (by omega)
      exact ⟨l₁, l₂ ++ [_], by simp, h₁, h₂.snoc hj⟩

/-- Shifting the words `i, …, j-1` onto a state. -/
theorem runFrom {red : Buffer Atom → Buffer Atom → Prop} {i j : ℕ} {l : Buffer Atom}
    (h : Words lex i j l) (st : Buffer Atom) : RunFrom red lex i st j (st ++ l) := by
  induction h with
  | refl => simpa using RunFrom.refl
  | snoc _ hj ih => simpa [← List.append_assoc] using ih.shift hj

end Words

/-- **Context-closed simulation.**  A derivation of `C` over `[i, j)` reduces the words of the
span to `C` *inside any product context* `L * ⋯ * R`. -/
theorem Derives.reduce_ctx {R : Rules Atom} {lex : Fin n → Cat Atom}
    (hu : ∀ C D : Cat Atom, ¬ R.unary C D) {i j : ℕ} {C : Cat Atom} (h : Derives R lex i j C)
    {l : Buffer Atom} (hl : Words lex i j l) (L Rt : Buffer Atom) :
    Relation.ReflTransGen (Reduce R.bin) (L ++ l ++ Rt) (L ++ C :: Rt) := by
  induction h generalizing l L Rt with
  | lex i₀ =>
    obtain ⟨hi, rfl⟩ := hl.succ_inv rfl
    have : (⟨i₀, hi⟩ : Fin n) = i₀ := Fin.ext rfl
    rw [this]
    simp only [List.append_assoc, List.singleton_append]
    exact Relation.ReflTransGen.refl
  | unary _ hCD => exact (hu _ _ hCD).elim
  | @bin i k j A B C h₁ h₂ hABC ih₁ ih₂ =>
    obtain ⟨l₁, l₂, rfl, hl₁, hl₂⟩ := hl.split k (le_of_lt h₁.lt) (le_of_lt h₂.lt)
    have s₁ := ih₁ hl₁ L (l₂ ++ Rt)
    have s₂ := ih₂ hl₂ (L ++ [A]) Rt
    simp only [List.append_assoc] at s₁ s₂
    simp only [List.append_assoc]
    exact (s₁.trans s₂).tail ⟨L, A, B, C, Rt, by simp, hABC, rfl⟩

/-- **The trivial product state is always continuable**: from the pure product of the first
`i` words, the remaining words can be shifted and the whole reduced to `C`. -/
theorem trivial_state_continues {R : Rules Atom} {lex : Fin n → Cat Atom}
    (hu : ∀ C D : Cat Atom, ¬ R.unary C D) {C : Cat Atom} (h : Derives R lex 0 n C)
    {i : ℕ} (hi : i ≤ n) {st : Buffer Atom} (hst : Words lex 0 i st) :
    RunFrom (Reduce R.bin) lex i st n [C] := by
  obtain ⟨l, hl⟩ := Words.exists_of_le (lex := lex) hi le_rfl
  have h₁ : RunFrom (Reduce R.bin) lex i st n (st ++ l) := hl.runFrom st
  have h₂ := h.reduce_ctx hu (hst.append hl) [] []
  simp only [List.nil_append, List.append_nil] at h₂
  exact h₁.trans (RunFrom.ofRTG h₂)

/-! ### Eager runs -/

/-- A state with no applicable reduction. -/
def Irreducible (red : Buffer Atom → Buffer Atom → Prop) (st : Buffer Atom) : Prop :=
  ∀ st', ¬ red st st'

/-- An eager run: after every shift, reduce until no reduction applies. -/
inductive EagerRun (red : Buffer Atom → Buffer Atom → Prop) (lex : Fin n → Cat Atom) :
    ℕ → Buffer Atom → Prop
  | start : EagerRun red lex 0 []
  | step {i : ℕ} {st st' : Buffer Atom} : EagerRun red lex i st → (hi : i < n) →
      Relation.ReflTransGen red (st ++ [lex ⟨i, hi⟩]) st' → Irreducible red st' →
      EagerRun red lex (i + 1) st'

theorem EagerRun.run {red : Buffer Atom → Buffer Atom → Prop} {lex : Fin n → Cat Atom} {i : ℕ}
    {st : Buffer Atom} (h : EagerRun red lex i st) : Run red lex i st := by
  induction h with
  | start => exact RunFrom.refl
  | step _ hi hr _ ih => exact (ih.shift hi).trans (RunFrom.ofRTG hr)

/-! ### Reductions of small buffers -/

section Small

variable {bin : Cat Atom → Cat Atom → Cat Atom → Prop}

theorem Reduce.not_nil {st' : Buffer Atom} : ¬ Reduce bin [] st' := by
  rintro ⟨L, A, B, C, R, h, -, -⟩
  cases L <;> simp at h

theorem Reduce.not_single {A : Cat Atom} {st' : Buffer Atom} : ¬ Reduce bin [A] st' := by
  rintro ⟨L, A', B', C, R, h, -, -⟩
  rcases L with _ | ⟨_, L⟩ <;> simp at h

theorem Reduce.pair_iff {A B : Cat Atom} {st' : Buffer Atom} :
    Reduce bin [A, B] st' ↔ ∃ C, bin A B C ∧ st' = [C] := by
  constructor
  · rintro ⟨L, A', B', C, R, h, hb, rfl⟩
    rcases L with _ | ⟨_, L⟩
    · simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨C, hb, rfl⟩
    · rcases L with _ | ⟨_, L⟩ <;> simp at h
  · rintro ⟨C, hb, rfl⟩
    exact ⟨[], A, B, C, [], rfl, hb, rfl⟩

theorem Reduce.triple_iff {A B D : Cat Atom} {st' : Buffer Atom} :
    Reduce bin [A, B, D] st' ↔ (∃ C, bin A B C ∧ st' = [C, D]) ∨ (∃ C, bin B D C ∧ st' = [A, C]) := by
  constructor
  · rintro ⟨L, A', B', C, R, h, hb, rfl⟩
    rcases L with _ | ⟨x, L⟩
    · simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inl ⟨C, hb, rfl⟩
    · rcases L with _ | ⟨y, L⟩
      · simp at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact Or.inr ⟨C, hb, rfl⟩
      · rcases L with _ | ⟨_, L⟩ <;> simp at h
  · rintro (⟨C, hb, rfl⟩ | ⟨C, hb, rfl⟩)
    · exact ⟨[], A, B, C, [D], rfl, hb, rfl⟩
    · exact ⟨[A], B, D, C, [], rfl, hb, rfl⟩

/-- A one-element buffer is irreducible. -/
theorem Irreducible.single (A : Cat Atom) : Irreducible (Reduce bin) [A] :=
  fun _ h => Reduce.not_single h

/-- A two-element buffer is irreducible iff its pair does not combine. -/
theorem Irreducible.pair {A B : Cat Atom} (h : ∀ C, ¬ bin A B C) : Irreducible (Reduce bin) [A, B] :=
  fun _ hr => let ⟨C, hC, _⟩ := Reduce.pair_iff.mp hr; h C hC

theorem Irreducible.triple {A B D : Cat Atom} (h₁ : ∀ C, ¬ bin A B C) (h₂ : ∀ C, ¬ bin B D C) :
    Irreducible (Reduce bin) [A, B, D] := by
  intro st' hr
  rcases Reduce.triple_iff.mp hr with ⟨C, hC, -⟩ | ⟨C, hC, -⟩
  · exact h₁ C hC
  · exact h₂ C hC

/-- The reflexive–transitive closure out of a two-element buffer with a *unique* reduct `[C]`
ends either there or in `[C]`. -/
theorem rtg_pair {A B C : Cat Atom} (hu : ∀ C', bin A B C' → C' = C) {st' : Buffer Atom}
    (h : Relation.ReflTransGen (Reduce bin) [A, B] st') : st' = [A, B] ∨ st' = [C] := by
  rcases h.cases_head with rfl | ⟨st₁, h₁, h₂⟩
  · exact Or.inl rfl
  · obtain ⟨C', hC', rfl⟩ := Reduce.pair_iff.mp h₁
    rw [hu C' hC'] at h₂
    rcases h₂.cases_head with rfl | ⟨_, h₃, -⟩
    · exact Or.inr rfl
    · exact (Reduce.not_single h₃).elim

end Small

end CCG
