import CCGPropFormalization.Product
import CCGPropFormalization.Audit.ASF

/-!
# Audit 8 — Product + Spine Application

System: `FA/BA + Bⁿ + Product + SA`  (`ProdBin`, runs over `Buffer`).

**Main theorem (true, but trivially).**  Every original derivation (FA/BA + Bⁿ, no unary rules)
is a strict left-to-right product run ending in `S` — even with the stack discipline
(`original_ccg_to_product_ltr`, `original_app_to_stack_ltr`).  The reason is that the product
state may stay *unreduced*: shift everything, then reduce in post-order of the original tree.
Consequently the trivial state `w₁ * ⋯ * wᵢ` is always reachable (`prefix_state_trivial`) and
always continuable to `S` (`product_grammAcceptable`): prefix reducibility and grammatical
acceptability hold for free, and SA is not even needed.

**The non-trivial version is eager reduction** (`EagerRun`: reduce to a normal form after every
shift).  It is **false**: for `John likes Mary madly` the eager run is forced through
`[S/NP]`, `[S]` and then gets stuck on `madly` (`lexAdj_not_eager`).  Eager runs do exist for
`NP NP (S\NP)\NP` and for `what apparently Mary likes` (`lexSOV_eager`, `lexWhatApp_eager`).

**Extra checks.**
* Generalized composition is still necessary: `S/(S/NP) S/S S/NP` derives `S` only through
  `B¹`; with FA/BA + Product + SA no reduction ever applies (`lexComp_not_run_appSA`).
* SA is strictly weaker than unrestricted ASP: `SA ⊆ ASP ; App` (`SA.asp_app`), and a functor
  selecting the permuted category `(S/NP)\NP` accepts `(S\NP)/NP` under ASP but not under SA
  (`lexPerm_not_run`).
* Product with reduction anywhere and the plain stack (`TopReduce`) have the same recognition
  power (both simulate all derivations); they differ only in which intermediate states are
  reachable.
-/

namespace CCG

open Cat

variable {Atom : Type}

/-! ### List helpers: locating a slot in a short spine -/

theorem append_cons_ne_nil {α : Type} (Γ Δ : List α) (x : α) : Γ ++ x :: Δ ≠ [] := by
  cases Γ <;> simp

theorem append_cons_eq_single {α : Type} {Γ Δ : List α} {x a : α} (h : Γ ++ x :: Δ = [a]) :
    Γ = [] ∧ x = a ∧ Δ = [] := by
  rcases Γ with _ | ⟨_, Γ⟩ <;> simp at h
  exact ⟨rfl, h.1, h.2⟩

theorem append_cons_eq_pair {α : Type} {Γ Δ : List α} {x a b : α} (h : Γ ++ x :: Δ = [a, b]) :
    (Γ = [] ∧ x = a ∧ Δ = [b]) ∨ (Γ = [a] ∧ x = b ∧ Δ = []) := by
  rcases Γ with _ | ⟨y, Γ⟩
  · simp at h; exact Or.inl ⟨rfl, h.1, h.2⟩
  · rcases Γ with _ | ⟨_, Γ⟩ <;> simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inr ⟨rfl, rfl, rfl⟩

/-- Inversion of an eager run after a shift. -/
theorem EagerRun.succ_inv {n : ℕ} {red : Buffer Atom → Buffer Atom → Prop} {lex : Fin n → Cat Atom}
    {i : ℕ} {st' : Buffer Atom} (h : EagerRun red lex (i + 1) st') :
    ∃ st, EagerRun red lex i st ∧ ∃ hi : i < n,
      Relation.ReflTransGen red (st ++ [lex ⟨i, hi⟩]) st' ∧ Irreducible red st' := by
  cases h with
  | step h hi hr hirr => exact ⟨_, h, hi, hr, hirr⟩

theorem rtg_single {bin : Cat Atom → Cat Atom → Cat Atom → Prop} {A : Cat Atom} {st' : Buffer Atom}
    (h : Relation.ReflTransGen (Reduce bin) [A] st') : st' = [A] := by
  rcases h.cases_head with rfl | ⟨_, h₁, -⟩
  · rfl
  · exact (Reduce.not_single h₁).elim

/-! ### The main theorem: trivially true -/

section Main

variable {n : ℕ} (lex : Fin n → Cat Atom)

/-- **Original CCG ⇒ left-to-right product run.**  Holds with the product buffer and SA… -/
theorem original_ccg_to_product_ltr {S : Cat Atom} (h : Derives Rules.noTR lex 0 n S) :
    Run (Reduce ProdBin) lex n [S] :=
  (h.runFrom (fun _ _ h => h) []).mono (fun _ _ hr => hr.reduce.mono (fun _ _ _ => Or.inl))

/-- …and already with a plain stack and the original binary rules only (no SA). -/
theorem original_ccg_to_stack_ltr {S : Cat Atom} (h : Derives Rules.noTR lex 0 n S) :
    Run (TopReduce Combine) lex n [S] :=
  h.runFrom (fun _ _ h => h) []

/-- For application-only derivations, FA/BA + Product suffice (no SA, no composition). -/
theorem original_app_to_stack_ltr {S : Cat Atom} (h : Derives Rules.app lex 0 n S) :
    Run (TopReduce App) lex n [S] :=
  h.runFrom (fun _ _ h => h) []

/-- **Prefix reducibility is trivial**: the pure product `w₁ * ⋯ * wᵢ` is always a reachable
state (shift only). -/
theorem prefix_state_trivial {red : Buffer Atom → Buffer Atom → Prop} (i : ℕ) (hi : i ≤ n) :
    ∃ st, Words lex 0 i st ∧ Run red lex i st :=
  let ⟨st, hst⟩ := Words.exists_of_le (lex := lex) (Nat.zero_le i) hi
  ⟨st, hst, by simpa using hst.runFrom (red := red) []⟩

/-- **Grammatical acceptability is trivial**: the pure product state of every prefix continues
to `S` (reduce anywhere). -/
theorem product_grammAcceptable {S : Cat Atom} (h : Derives Rules.noTR lex 0 n S) (i : ℕ)
    (hi : i ≤ n) : ∃ st, Run (Reduce ProdBin) lex i st ∧ RunFrom (Reduce ProdBin) lex i st n [S] :=
  let ⟨st, hst, hrun⟩ := prefix_state_trivial lex (red := Reduce ProdBin) i hi
  ⟨st, hrun, (trivial_state_continues (fun _ _ h => h) h hi hst).mono
    (fun _ _ hr => hr.mono (fun _ _ _ => Or.inl))⟩

end Main

/-! ### Concrete lexica -/

/-- An atom has no slot. -/
theorem flatten_atom_no_slot {a : Atom} {H : Cat Atom} {Γ Δ : List (ArgSlot Atom)} {x : ArgSlot Atom}
    (h : flattenSpine (atom a) = (H, Γ ++ x :: Δ)) : False := by
  simp only [flattenSpine_atom, Prod.mk.injEq] at h
  exact append_cons_ne_nil _ _ _ h.2.symm

/-- Tactic for closing a `Combine.inv` case that is a constructor clash in `h₁` or `h₂`. -/
macro "combine_clash" a:ident b:ident : tactic =>
  `(tactic| first
    | (cases $a:ident; done)
    | (cases $b:ident; done)
    | (cases $a:ident; cases $b:ident; done)
    | (cases $b:ident; cases $a:ident; done)
    | exact absurd ($a:ident).symm (slash_ne_atom _ _ _ _)
    | exact absurd ($b:ident).symm (slash_ne_atom _ _ _ _)
    | exact slash_ne_atom _ _ _ _ $a:ident
    | exact slash_ne_atom _ _ _ _ $b:ident)

/-- Close a goal from `h : atom x = atom y` (either orientation) and `hsn : y ≠ x`. -/
macro "atom_clash" h:ident hsn:ident : tactic =>
  `(tactic| first
    | exact $hsn:ident (Cat.atom.inj $h:ident)
    | exact $hsn:ident (Cat.atom.inj $h:ident).symm)

section Concrete

variable (s np : Atom)

local notation "S" => atom s
local notation "NP" => atom np

/-- `NP  (S\NP)/NP ⇒ S/NP` by SA on the inner backward slot. -/
theorem sa_np_likes : SA NP ((S ⧵ NP) ⫽ NP) (S ⫽ NP) := by
  have h := SA.left (A := NP) (F := (S ⧵ NP) ⫽ NP) (H := S) (Γ := []) (Δ := [⟨.fwd, NP⟩]) (by simp)
  simpa using h

/-- `S/(S/NP)  S/S  S/NP`. -/
def lexComp : Fin 3 → Cat Atom := ![S ⫽ (S ⫽ NP), S ⫽ S, S ⫽ NP]

theorem lexComp_full : Derives Rules.noTR (lexComp s np) 0 3 S :=
  Derives.bin (Derives.lex 0)
    (Derives.bin (Derives.lex 1) (Derives.lex 2) (Combine.fcomp₁ S S NP))
    (Combine.fa S (S ⫽ NP))

/-- `(S\NP)/NP` followed by a functor selecting the *permuted* category `(S/NP)\NP`. -/
def lexPerm : Fin 2 → Cat Atom := ![(S ⧵ NP) ⫽ NP, S ⧵ ((S ⫽ NP) ⧵ NP)]

/-- Under FA/BA + ASP the sentence derives `S`. -/
theorem lexPerm_appAsp : Derives Rules.appAsp (lexPerm s np) 0 2 S :=
  Derives.bin ((Derives.lex 0).unary (ASP.bwd_fwd S NP NP)) (Derives.lex 1)
    (App.ba S ((S ⫽ NP) ⧵ NP))

variable {s np}

/-- The only reduct of `NP  (S\NP)/NP` is `S/NP`. -/
theorem prodBin_np_likes {C : Cat Atom} (h : ProdBin NP ((S ⧵ NP) ⫽ NP) C) : C = S ⫽ NP := by
  rcases h with h | h
  · exfalso
    rcases h.inv with ⟨X, Y, h₁, h₂, h₃⟩ | ⟨X, Y, h₁, h₂, h₃⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩ | ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩
    all_goals combine_clash h₁ h₂
  · rcases h.inv with ⟨H, Γ, Δ, h₁, rfl⟩ | ⟨H, Γ, Δ, h₁, -⟩
    · simp only [flattenSpine_fwd, flattenSpine_bwd, flattenSpine_atom, List.nil_append,
        List.singleton_append, Prod.mk.injEq] at h₁
      obtain ⟨rfl, h₁⟩ := h₁
      rcases append_cons_eq_pair h₁.symm with ⟨rfl, -, rfl⟩ | ⟨-, h₂, -⟩
      · rfl
      · have h₃ := (ArgSlot.mk.inj h₂).1; cases h₃
    · exact (flatten_atom_no_slot h₁).elim

/-- The only reduct of `S/NP  NP` is `S`. -/
theorem prodBin_sNP_np {C : Cat Atom} (h : ProdBin (S ⫽ NP) NP C) : C = S := by
  rcases h with h | h
  · rcases h.inv with ⟨X, Y, h₁, h₂, h₃⟩ | ⟨X, Y, h₁, h₂, h₃⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩ | ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩
    · cases h₁; exact h₃
    all_goals (exfalso; combine_clash h₁ h₂)
  · rcases h.inv with ⟨H, Γ, Δ, h₁, -⟩ | ⟨H, Γ, Δ, h₁, rfl⟩
    · exact (flatten_atom_no_slot h₁).elim
    · simp only [flattenSpine_fwd, flattenSpine_atom, List.nil_append, Prod.mk.injEq] at h₁
      obtain ⟨rfl, h₁⟩ := h₁
      obtain ⟨rfl, -, rfl⟩ := append_cons_eq_single h₁.symm
      rfl

/-- `S` and `(S\NP)\(S\NP)` never combine. -/
theorem prodBin_S_madly (hsn : np ≠ s) {C : Cat Atom} : ¬ ProdBin S ((S ⧵ NP) ⧵ (S ⧵ NP)) C := by
  rintro (h | h)
  · rcases h.inv with ⟨X, Y, h₁, h₂, h₃⟩ | ⟨X, Y, h₁, h₂, h₃⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩ | ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩
    all_goals combine_clash h₁ h₂
  · rcases h.inv with ⟨H, Γ, Δ, h₁, -⟩ | ⟨H, Γ, Δ, h₁, -⟩
    · simp only [flattenSpine_bwd, flattenSpine_atom, List.nil_append, List.singleton_append,
        Prod.mk.injEq] at h₁
      have h₂ := h₁.2
      rcases append_cons_eq_pair h₂.symm with ⟨-, h₃, -⟩ | ⟨-, h₃, -⟩
      · have h₄ := (ArgSlot.mk.inj h₃).2
        atom_clash h₄ hsn
      · have h₄ := (ArgSlot.mk.inj h₃).2; cases h₄
    · exact (flatten_atom_no_slot h₁).elim

/-! #### The eager counterexample: `John likes Mary madly` -/

local notation "Rp" => Reduce (ProdBin (Atom := Atom))

theorem lexAdj_eager₁ {st : Buffer Atom} (h : EagerRun Rp (lexAdj s np) 1 st) : st = [NP] := by
  obtain ⟨st₀, h₀, hi, hr, -⟩ := h.succ_inv
  cases h₀
  exact rtg_single hr

theorem lexAdj_eager₂ {st : Buffer Atom} (h : EagerRun Rp (lexAdj s np) 2 st) : st = [S ⫽ NP] := by
  obtain ⟨st₁, h₁, hi, hr, hirr⟩ := h.succ_inv
  rw [lexAdj_eager₁ h₁] at hr
  have hr : Relation.ReflTransGen Rp [NP, (S ⧵ NP) ⫽ NP] st := hr
  rcases rtg_pair (fun _ h => prodBin_np_likes h) hr with h₂ | h₂
  · subst h₂
    exact (hirr _ (Reduce.pair_iff.mpr ⟨_, Or.inr (sa_np_likes s np), rfl⟩)).elim
  · exact h₂

theorem lexAdj_eager₃ {st : Buffer Atom} (h : EagerRun Rp (lexAdj s np) 3 st) : st = [S] := by
  obtain ⟨st₂, h₂, hi, hr, hirr⟩ := h.succ_inv
  rw [lexAdj_eager₂ h₂] at hr
  have hr : Relation.ReflTransGen Rp [S ⫽ NP, NP] st := hr
  rcases rtg_pair (fun _ h => prodBin_sNP_np h) hr with h₃ | h₃
  · subst h₃
    exact (hirr _ (Reduce.pair_iff.mpr ⟨_, Or.inl (Combine.fa S NP), rfl⟩)).elim
  · exact h₃

theorem lexAdj_eager₄ (hsn : np ≠ s) {st : Buffer Atom} (h : EagerRun Rp (lexAdj s np) 4 st) :
    st = [S, (S ⧵ NP) ⧵ (S ⧵ NP)] := by
  obtain ⟨st₃, h₃, hi, hr, -⟩ := h.succ_inv
  rw [lexAdj_eager₃ h₃] at hr
  have hr : Relation.ReflTransGen Rp [S, (S ⧵ NP) ⧵ (S ⧵ NP)] st := hr
  rcases hr.cases_head with h₄ | ⟨_, h₁, -⟩
  · exact h₄.symm
  · obtain ⟨C, hC, -⟩ := Reduce.pair_iff.mp h₁
    exact (prodBin_S_madly hsn hC).elim

/-- **Eager left-to-right reduction fails on right adjunction**: the sentence has a lazy product
run to `S` (it even has an FA/BA derivation), but no eager run reaches `[S]`. -/
theorem lexAdj_not_eager (hsn : np ≠ s) :
    Run Rp (lexAdj s np) 4 [S] ∧ ¬ EagerRun Rp (lexAdj s np) 4 [S] :=
  ⟨original_ccg_to_product_ltr _ ((lexAdj_full s np).mono Rules.app_le_noTR),
    fun h => by have := lexAdj_eager₄ hsn h; cases this⟩

/-! #### Positive eager runs -/

/-- `NP NP` never combine (no slots on either side). -/
theorem prodBin_np_np {C : Cat Atom} : ¬ ProdBin NP NP C := by
  rintro (h | h)
  · exact Combine.not_atom_atom np np ⟨C, h⟩
  · rcases h.inv with ⟨H, Γ, Δ, h₁, -⟩ | ⟨H, Γ, Δ, h₁, -⟩ <;> exact flatten_atom_no_slot h₁

/-- `NP NP (S\NP)\NP`: eager run `[NP] → [NP, NP] → [S]`. -/
theorem lexSOV_eager : EagerRun Rp (lexSOV s np) 3 [S] := by
  have e₁ : EagerRun Rp (lexSOV s np) 1 [NP] :=
    EagerRun.start.step (by omega) Relation.ReflTransGen.refl (Irreducible.single _)
  have e₂ : EagerRun Rp (lexSOV s np) 2 [NP, NP] :=
    e₁.step (by omega) Relation.ReflTransGen.refl (Irreducible.pair fun _ => prodBin_np_np)
  refine e₂.step (by omega) ?_ (Irreducible.single _)
  have r₁ : Rp [NP, NP, (S ⧵ NP) ⧵ NP] [NP, S ⧵ NP] :=
    ⟨[NP], NP, (S ⧵ NP) ⧵ NP, S ⧵ NP, [], rfl, Or.inl (Combine.ba (S ⧵ NP) NP), rfl⟩
  have r₂ : Rp [NP, S ⧵ NP] [S] := ⟨[], NP, S ⧵ NP, S, [], rfl, Or.inl (Combine.ba S NP), rfl⟩
  exact (Relation.ReflTransGen.single r₁).tail r₂

/-- `S/(S/NP)` and `S/S` never combine (head mismatch; no SA slot matches). -/
theorem prodBin_what_app (hsn : np ≠ s) {C : Cat Atom} : ¬ ProdBin (S ⫽ (S ⫽ NP)) (S ⫽ S) C := by
  rintro (h | h)
  · rcases h.inv with ⟨X, Y, h₁, h₂, h₃⟩ | ⟨X, Y, h₁, h₂, h₃⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩ | ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩
    · cases h₁
      have h₄ := (Cat.fwd.inj h₂).2
      atom_clash h₄ hsn
    · cases h₂
    · cases h₁
      rw [eq_comm, slash_eq_fwd_iff] at h₂
      obtain ⟨rfl, rfl, rfl⟩ := h₂
      have h₄ := (hr.atom_left rfl).1; cases h₄
    · cases h₂
  · rcases h.inv with ⟨H, Γ, Δ, h₁, -⟩ | ⟨H, Γ, Δ, h₁, -⟩
    · simp only [flattenSpine_fwd, flattenSpine_atom, List.nil_append, Prod.mk.injEq] at h₁
      have h₂ := (append_cons_eq_single h₁.2.symm).2.1
      have h₃ := (ArgSlot.mk.inj h₂).1; cases h₃
    · simp only [flattenSpine_fwd, flattenSpine_atom, List.nil_append, Prod.mk.injEq] at h₁
      have h₂ := (append_cons_eq_single h₁.2.symm).2.1
      have h₃ := (Cat.fwd.inj (ArgSlot.mk.inj h₂).2).2
      atom_clash h₃ hsn

/-- `S/S` and `NP` never combine. -/
theorem prodBin_app_np (hsn : np ≠ s) {C : Cat Atom} : ¬ ProdBin (S ⫽ S) NP C := by
  rintro (h | h)
  · rcases h.inv with ⟨X, Y, h₁, h₂, h₃⟩ | ⟨X, Y, h₁, h₂, h₃⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩ | ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩
    · cases h₁; atom_clash h₂ hsn
    all_goals combine_clash h₁ h₂
  · rcases h.inv with ⟨H, Γ, Δ, h₁, -⟩ | ⟨H, Γ, Δ, h₁, -⟩
    · exact flatten_atom_no_slot h₁
    · simp only [flattenSpine_fwd, flattenSpine_atom, List.nil_append, Prod.mk.injEq] at h₁
      have h₂ := (append_cons_eq_single h₁.2.symm).2.1
      have h₃ := (ArgSlot.mk.inj h₂).2
      atom_clash h₃ hsn

/-- `what apparently Mary likes`: eager run
`[what] → [what, app] → [what, app, NP] → [what, app, S/NP] → [what, S/NP] → [S]`. -/
theorem lexWhatApp_eager (hsn : np ≠ s) : EagerRun Rp (lexWhatApp s np) 4 [S] := by
  have e₁ : EagerRun Rp (lexWhatApp s np) 1 [S ⫽ (S ⫽ NP)] :=
    EagerRun.start.step (by omega) Relation.ReflTransGen.refl (Irreducible.single _)
  have e₂ : EagerRun Rp (lexWhatApp s np) 2 [S ⫽ (S ⫽ NP), S ⫽ S] :=
    e₁.step (by omega) Relation.ReflTransGen.refl (Irreducible.pair fun _ => prodBin_what_app hsn)
  have e₃ : EagerRun Rp (lexWhatApp s np) 3 [S ⫽ (S ⫽ NP), S ⫽ S, NP] :=
    e₂.step (by omega) Relation.ReflTransGen.refl
      (Irreducible.triple (fun _ => prodBin_what_app hsn) (fun _ => prodBin_app_np hsn))
  refine e₃.step (by omega) ?_ (Irreducible.single _)
  have r₁ : Rp [S ⫽ (S ⫽ NP), S ⫽ S, NP, (S ⧵ NP) ⫽ NP] [S ⫽ (S ⫽ NP), S ⫽ S, S ⫽ NP] :=
    ⟨[S ⫽ (S ⫽ NP), S ⫽ S], NP, (S ⧵ NP) ⫽ NP, S ⫽ NP, [], rfl, Or.inr (sa_np_likes s np), rfl⟩
  have r₂ : Rp [S ⫽ (S ⫽ NP), S ⫽ S, S ⫽ NP] [S ⫽ (S ⫽ NP), S ⫽ NP] :=
    ⟨[S ⫽ (S ⫽ NP)], S ⫽ S, S ⫽ NP, S ⫽ NP, [], rfl, Or.inl (Combine.fcomp₁ S S NP), rfl⟩
  have r₃ : Rp [S ⫽ (S ⫽ NP), S ⫽ NP] [S] :=
    ⟨[], S ⫽ (S ⫽ NP), S ⫽ NP, S, [], rfl, Or.inl (Combine.fa S (S ⫽ NP)), rfl⟩
  exact ((Relation.ReflTransGen.single r₁).tail r₂).tail r₃

/-! #### Generalized composition is still necessary -/

/-- `S/S` and `S/NP` do not combine by FA/BA/SA. -/
theorem appSA_app_sNP {C : Cat Atom} : ¬ AppSA (S ⫽ S) (S ⫽ NP) C := by
  rintro (h | h)
  · cases h
  · rcases h.inv with ⟨H, Γ, Δ, h₁, -⟩ | ⟨H, Γ, Δ, h₁, -⟩
    · simp only [flattenSpine_fwd, flattenSpine_atom, List.nil_append, Prod.mk.injEq] at h₁
      have h₂ := (append_cons_eq_single h₁.2.symm).2.1
      have h₃ := (ArgSlot.mk.inj h₂).1; cases h₃
    · simp only [flattenSpine_fwd, flattenSpine_atom, List.nil_append, Prod.mk.injEq] at h₁
      have h₂ := (append_cons_eq_single h₁.2.symm).2.1
      have h₃ := (ArgSlot.mk.inj h₂).2; cases h₃

theorem appSA_what_app (hsn : np ≠ s) {C : Cat Atom} : ¬ AppSA (S ⫽ (S ⫽ NP)) (S ⫽ S) C :=
  fun h => prodBin_what_app hsn h.prodBin

/-- Every state of a run over `lexComp` with FA/BA + SA is a pure prefix product. -/
theorem lexComp_run_words (hsn : np ≠ s) {i : ℕ} {st : Buffer Atom}
    (h : Run (Reduce AppSA) (lexComp s np) i st) : Words (lexComp s np) 0 i st := by
  generalize hi : (0 : ℕ) = i₀ at h
  generalize hst : ([] : Buffer Atom) = st₀ at h
  induction h with
  | refl => subst hi hst; exact Words.refl
  | shift _ hj ih => exact ih.snoc hj
  | @reduce j st' st'' h hr ih =>
    exfalso
    subst hi hst
    have hw := ih
    obtain ⟨L, A, B, C, R, hst', hb, -⟩ := hr
    rcases hw with _ | ⟨hw, hj₁⟩
    · cases L <;> simp at hst'
    rcases hw with _ | ⟨hw, hj₂⟩
    · rcases L with _ | ⟨_, L⟩ <;> simp at hst'
    rcases hw with _ | ⟨hw, hj₃⟩
    · obtain ⟨C', hC', -⟩ := Reduce.pair_iff.mp ⟨L, A, B, C, R, hst', hb, rfl⟩
      exact appSA_what_app hsn hC'
    rcases hw with _ | ⟨hw, hj₄⟩
    · rcases Reduce.triple_iff.mp ⟨L, A, B, C, R, hst', hb, rfl⟩ with ⟨C', hC', -⟩ | ⟨C', hC', -⟩
      · exact appSA_what_app hsn hC'
      · exact appSA_app_sNP hC'
    omega

/-- **Composition is necessary**: `S/(S/NP) S/S S/NP` derives `S` with `B¹`, but no product run
with FA/BA + SA reaches `[S]`. -/
theorem lexComp_not_run_appSA (hsn : np ≠ s) :
    Derives Rules.noTR (lexComp s np) 0 3 S ∧ ¬ Run (Reduce AppSA) (lexComp s np) 3 [S] :=
  ⟨lexComp_full s np, fun h => by
    have := (lexComp_run_words hsn h).length
    simp at this⟩

/-! #### SA is strictly weaker than ASP -/

theorem prodBin_perm (hsn : np ≠ s) {C : Cat Atom} :
    ¬ ProdBin ((S ⧵ NP) ⫽ NP) (S ⧵ ((S ⫽ NP) ⧵ NP)) C := by
  rintro (h | h)
  · rcases h.inv with ⟨X, Y, h₁, h₂, h₃⟩ | ⟨X, Y, h₁, h₂, h₃⟩ |
        ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩ | ⟨X, Y, A', B', s', Z', hr, h₁, h₂, h₃⟩
    · cases h₁; cases h₂
    · cases h₂; cases h₁
    · cases h₁
      rw [eq_comm, slash_eq_bwd_iff] at h₂
      obtain ⟨rfl, rfl, rfl⟩ := h₂
      have h₄ := (hr.atom_left rfl).1
      atom_clash h₄ hsn
    · cases h₂
      rw [eq_comm, slash_eq_fwd_iff] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      rcases hr.inv with ⟨h₃, -⟩ | ⟨s'', Z'', A'', B'', hr', h₃, -⟩
      · cases h₃
      · rw [eq_comm, slash_eq_bwd_iff] at h₃
        obtain ⟨rfl, rfl, rfl⟩ := h₃
        have h₄ := (hr'.atom_left rfl).1; cases h₄
  · rcases h.inv with ⟨H, Γ, Δ, h₁, -⟩ | ⟨H, Γ, Δ, h₁, -⟩
    · simp only [flattenSpine_bwd, flattenSpine_atom, List.nil_append, Prod.mk.injEq] at h₁
      have h₂ := (append_cons_eq_single h₁.2.symm).2.1
      have h₃ := (ArgSlot.mk.inj h₂).2; cases h₃
    · simp only [flattenSpine_fwd, flattenSpine_bwd, flattenSpine_atom, List.nil_append,
        List.singleton_append, Prod.mk.injEq] at h₁
      rcases append_cons_eq_pair h₁.2.symm with ⟨-, h₂, -⟩ | ⟨-, h₂, -⟩
      · have h₃ := (ArgSlot.mk.inj h₂).1; cases h₃
      · have h₃ := (ArgSlot.mk.inj h₂).2; cases h₃

/-- **SA is strictly weaker than ASP**: with the product system (FA/BA + Bⁿ + SA) the two words
never combine, so no run reaches `[S]`. -/
theorem lexPerm_not_run (hsn : np ≠ s) : ¬ Run (Reduce ProdBin) (lexPerm s np) 2 [S] := by
  intro h
  have key : ∀ {i : ℕ} {st : Buffer Atom}, Run (Reduce ProdBin) (lexPerm s np) i st →
      Words (lexPerm s np) 0 i st := by
    intro i st h
    generalize hi : (0 : ℕ) = i₀ at h
    generalize hst : ([] : Buffer Atom) = st₀ at h
    induction h with
    | refl => subst hi hst; exact Words.refl
    | shift _ hj ih => exact ih.snoc hj
    | @reduce j st' st'' h hr ih =>
      exfalso
      subst hi hst
      have hw := ih
      obtain ⟨L, A, B, C, R, hst', hb, -⟩ := hr
      rcases hw with _ | ⟨hw, hj₁⟩
      · cases L <;> simp at hst'
      rcases hw with _ | ⟨hw, hj₂⟩
      · rcases L with _ | ⟨_, L⟩ <;> simp at hst'
      rcases hw with _ | ⟨hw, hj₃⟩
      · obtain ⟨C', hC', -⟩ := Reduce.pair_iff.mp ⟨L, A, B, C, R, hst', hb, rfl⟩
        exact prodBin_perm hsn hC'
      omega
  have := (key h).length
  simp at this

end Concrete

end CCG
