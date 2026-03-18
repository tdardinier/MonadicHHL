import MonadicHHL.Language

/-
abbrev hyperassertion (α val : Type) : Type
:= Set (Option val × State α) → Prop
-/


-------------------------------------------------
----------------- Loop stuff --------------------
-------------------------------------------------



lemma while_same_as_loop_HypraM {α : Type} (b : BExp α)
    (C : HypraM α Unit) :
  (do
     while ← HypraM.evalBExp b do C)
  = (do HypraM.loop_unit (do HypraM.assume b; C); HypraM.assume (LNot b))
:= by
  apply funext
  intro x
  simp [HypraM.loop_unit, Bind.bind, HypraM.bind, HypraM.assume, LNot]
  apply Set.ext
  intro y
  apply Iff.intro
  {
    simp
    intro x y h
    simp [forIn] at h

  }
















def WhileSuccesses {α : Type} (b : BExp α) (C : HypraM α Unit) (σ₀ : State α) :
    Set (Option Unit × State α) :=
  { (some (), σ_k) | (∃ (k : ℕ) (σs : Fin (k+1) → State α),
        σs ⟨0, Nat.succ_pos _⟩ = σ₀ ∧
        (∀ (i : Fin k),
          b (σs ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self k)⟩) = true ∧
          (some (), σs ⟨i.1.succ, Nat.succ_lt_succ i.2⟩)
            ∈ C (σs ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self k)⟩)) ∧
        b (σs ⟨k, Nat.lt_succ_self k⟩) = false ∧
        σ_k = σs ⟨k, Nat.lt_succ_self k⟩) }





open Lean

/--
Unfold a single step of the `forIn Loop.mk` loop for `β = PUnit`.

This works in *any* monad `m`. It gives you the standard
“either exit now, or do one more step and loop again” shape.
-/
lemma Loop.forIn_unfold_once
    {m : Type u → Type v} [Monad m]
    (f : Unit → PUnit → m (ForInStep PUnit)) :
  (do
      forIn Loop.mk PUnit.unit f
      pure PUnit.unit : m PUnit)
  =
  (do
      let step ← f () PUnit.unit
      match step with
      | ForInStep.done _  =>
          pure PUnit.unit
      | ForInStep.yield _ =>
          -- loop again
          (do
             forIn Loop.mk PUnit.unit f
             pure PUnit.unit) : m PUnit) := by
  -- Expand the `do` notation on both sides
  -- Left side:
  --   do forIn Loop.mk _ f; pure PUnit.unit
  -- ≃ (forIn Loop.mk _ f) >>= fun _ => pure PUnit.unit
  -- Right side:
  --   do step ← f _ _;
  --      match step with
  --      | done _  => pure PUnit.unit
  --      | yield _ => do forIn Loop.mk _ f; pure PUnit.unit
  -- ≃ f _ _ >>= fun step =>
  --       match step with
  --       | done _  => pure PUnit.unit
  --       | yield _ => (forIn Loop.mk _ f >>= fun _ => pure PUnit.unit)
  --
  -- Now unfold `forIn` in terms of `Loop.forIn` and its definition.
  --
  -- NOTE: `forIn` here is resolved via the instance
  --   instance : ForIn m Loop Unit where forIn := Loop.forIn
  --
  -- so `forIn Loop.mk ... f` is defeq to `Loop.forIn Loop.mk ... f`.
  --
  simp [ForIn.forIn, Loop.forIn]

 --  Bind.bind, Pure.pure, Seq.seq,
  --      SeqLeft.seqLeft, SeqRight.seqRight]



/--
  The main unfolding lemma you asked for:

  `while b do C` is equal to:
  `branch (assume ¬b) (assume b; C; while b do C)`.

  This is the “either exit, or do one more step” characterization.
-/
lemma while_unfold_HypraM {α : Type}
    (b : BExp α) (C : HypraM α Unit) :
  (do
     while ← HypraM.evalBExp b do
       C)
  =
  HypraM.branch
    (HypraM.assume (LNot b))
    (do
       HypraM.assume b
       C
       while ← HypraM.evalBExp b do
         C)
:= by
  /- High-level proof strategy:

     1. Expand the `while` in terms of `Loop.forIn`.
     2. Characterize `Loop.forIn` as the least fixpoint of the
        "either exit, or yield and continue" transformer.
     3. Show that the RHS is also a fixpoint of that transformer.
     4. Conclude equality by fixpoint uniqueness.

     Below, I sketch the essential steps and leave the heavy lifting
     (the fixpoint / iteration reasoning) as `sorry`, since it's a
     self-contained but non-trivial inductive argument on the number
     of `yield` steps.
  -/

  -- Step 1: work pointwise in the initial state
  funext σ
  apply Set.ext
  intro p
  constructor
  · intro hp
    /- Direction (→):

       From a run of Lean's built-in `while` to membership in the
       union of:

         - exit branch: `assume (¬b)`
         - step branch: `assume b; C; while ...`

       After macro expansion, the `while` loop is essentially:

         Loop.forIn Loop.mk () (fun _ _ =>
           do cond ← HypraM.evalBExp b
              if cond then
                C >> pure (ForInStep.yield ())
              else
                pure (ForInStep.done ()))

       You now prove, by induction on the number of `yield` steps,
       that:

       - either the loop exits immediately, yielding a state in
         `assume (¬b) σ`, or
       - it takes one step of `assume b; C` and then continues
         with another run of the same `while`.

       This matches exactly membership in the RHS set.

       The detailed proof is a bit long, but completely standard
       once you expand the forIn/Loop behavior.
    -/
    sorry
  · intro hp
    /- Direction (←):

       Conversely, given that `p` comes from either:

         - `assume (¬b)`, or
         - `assume b; C; while ...`,

       you can construct a corresponding finite run of the `while`
       loop:

       - in the first case, zero iterations: the first condition
         check fails and we exit immediately;
       - in the second case, one successful condition check and
         one execution of `C`, followed by a recursive run of `while`.

       Again, you fold this into the semantics of `Loop.forIn`
       (or equivalently, into a suitable number of `yield` steps
       followed by a `done`), and conclude that `p` is in the LHS set.

       This is the inverse inductive argument to the one above.
    -/
    sorry




























lemma while_unfold_HypraM {α : Type} (b : BExp α) (C : HypraM α Unit) :
  (do
    while ← HypraM.evalBExp b do C)
  =
  HypraM.branch
    (do
       HypraM.assume b
       C
       while ← HypraM.evalBExp b do
         C)
    (HypraM.assume (LNot b)) :=
by
  sorry


lemma while_same_as_loop_HypraM {α : Type} (b : BExp α)
    (C : HypraM α Unit) :
  (do
     while ← HypraM.evalBExp b do C)
     =
        (do (HypraM.loop_unit (do HypraM.assume b; C); HypraM.assume (LNot b)))
    := sorry





-------- Language ----------


inductive FStmt (α : Type) (v : Type) : Type where
  -- Core Monadic Operations
  | bind : FStmt α v₁ → (v₁ → FStmt α v) → FStmt α v
  | pure : v → FStmt α v

  -- State Operations (The new "primitives" that return a value)
  | get_state : FStmt α α                          -- Returns the current state (α)
  | put_state : α → FStmt α Unit                   -- Sets the state (returns Unit)

  -- Original state-modifying operations (now using `Unit` return)
  | assign : Var → Exp α → FStmt α Unit
  | havoc : Var → FStmt α Unit

  -- Control Flow
  | branch : FStmt α v → FStmt α v → FStmt α v
  | loop : FStmt α Unit → FStmt α Unit
  | assume : BExp α → FStmt α Unit
  | assert : BExp α → FStmt α Unit

-- inductive cases
inductive Expr (α val : Type) where
  | const : val → Expr α val
  | var : Var → Expr α val
  | bind : Expr α val → (val → Expr α val) → Expr α val






inductive Stmt (α : Type) : Type where
  | havoc : Var → Stmt α
  | branch : Stmt α → Stmt α → Stmt α
  | loop : Stmt α → Stmt α

infixr:90 "; " => Stmt.seq

def IfThenElse {α : Type} (b : BExp α) (C₁ C₂ : Stmt α) : Stmt α :=
  Stmt.branch (Stmt.assume b; C₁) (Stmt.assume (LNot b); C₂)

def While {α : Type} (b : BExp α) (C : Stmt α) : Stmt α :=
  Stmt.loop (Stmt.assume b; C); Stmt.assume (LNot b)


@[grind]
inductive BigStep {α : Type} : Stmt α → State α → State α → Prop where
  | skip (σ) :
    BigStep Stmt.skip σ σ
  | assign (x e σ) :
    BigStep (Stmt.assign x e) σ (σ[x ↦ e σ])
  | havoc (x v σ) :
    BigStep (Stmt.havoc x) σ (σ[x ↦ v])
  | seq (C₁ C₂ σ σ' σ'') (hS : BigStep C₁ σ σ'')
      (hT : BigStep C₂ σ'' σ') :
    BigStep (C₁; C₂) σ σ'
  | branch_left (C₁ C₂ σ σ')
      (hbody : BigStep C₁ σ σ') :
    BigStep (Stmt.branch C₁ C₂) σ σ'
  | branch_right (C₁ C₂ σ σ')
      (hbody : BigStep C₂ σ σ') :
    BigStep (Stmt.branch C₁ C₂) σ σ'
  | loop_more (C σ σ'' σ') (hbody : BigStep C σ σ'')
      (hrest : BigStep (Stmt.loop C) σ'' σ') :
    BigStep (Stmt.loop C) σ σ'
  | loop_exit (C σ) :
    BigStep (Stmt.loop C) σ σ
  | assume_true (b σ) (hcond : b σ) :
    BigStep (Stmt.assume b) σ σ

notation:65 "⟨" C ", " σ "⟩" " ⟹ " σ' => BigStep C σ σ'

def sem {α : Type} (C : Stmt α) (S : Set (State α)) : Set (State α) :=
  {σ' | ∃ σ, S σ ∧ ⟨C, σ⟩ ⟹ σ' }

@[grind =]
lemma sem_iff {α : Type} (σ' : State α) C S :
  sem C S σ' ↔ ∃σ, S σ ∧ ⟨C, σ⟩ ⟹ σ' :=
  by
    rw [sem]
    aesop

lemma in_semI {α : Type} (C : Stmt α) (S : Set (State α)) (σ' : State α) :
  (∃ σ, S σ ∧ ⟨C, σ⟩ ⟹ σ') → sem C S σ' :=
  by
  intro h
  simp [sem_iff]
  aesop

lemma in_semE {α : Type} {C : Stmt α} {S σ'} (h : sem C S σ') :
  ∃σ, S σ ∧ ⟨C, σ⟩ ⟹ σ' :=
  by
  have h := sem_iff σ'
  aesop

@[simp]
lemma sem_skip {α : Type} (S : Set (State α)) :
    sem Stmt.skip S = S := by
  apply funext
  grind

@[simp]
lemma sem_seq {α : Type} (C₁ C₂ : Stmt α) (S : Set (State α)) :
    sem (C₁; C₂) S = sem C₂ (sem C₁ S) := by
  apply funext
  grind

lemma bigstep_branch_iff {α : Type} (C₁ C₂ : Stmt α) (σ σ' : State α) :
    (⟨C₁, σ⟩ ⟹ σ') ∨ (⟨C₂, σ⟩ ⟹ σ') ↔ ⟨Stmt.branch C₁ C₂, σ⟩ ⟹ σ' :=
  by
  grind

@[grind =]
lemma in_union_iff {α : Type} (S₁ S₂ : Set (State α)) (σ' : State α) :
    (S₁ ∪ S₂) σ' ↔ S₁ σ' ∨ S₂ σ' :=
  by
  aesop

@[simp]
lemma sem_branch {α : Type} (C₁ C₂ : Stmt α) (S : Set (State α)) :
    sem (Stmt.branch C₁ C₂) S = sem C₁ S ∪ sem C₂ S := by
  apply funext
  grind

@[grind .]
lemma sem_mono {α : Type} (C : Stmt α) {S₁ S₂ : Set (State α)} :
    S₁ ⊆ S₂ → sem C S₁ ⊆ sem C S₂ :=
  by
  intro hσ σ' in_sem_C
  rcases in_sem_C with ⟨σ, in_S1, step⟩
  apply Exists.intro σ
  apply And.intro
  { apply hσ
    exact in_S1 }
  { exact step }

@[grind =]
lemma subset_iff {α : Type} (S S' : Set α) :
  S ⊆ S' ↔ ∀ x, S x → S' x :=
  by
  aesop

lemma subsetI {α : Type} {S S' : Set α} :
  (∀ x, S x → S' x) → S ⊆ S' :=
  by
    intro x h1 h2
    apply (subset_iff S S').mpr
    · exact x
    exact h2

/-
  | loop_more (C σ σ'' σ') (hbody : BigStep (C, σ) σ'')
      (hrest : BigStep (Stmt.loop C, σ'') σ') :
    BigStep (Stmt.loop C, σ) σ'
-/
lemma BigStep.loop_more_symm {α : Type} {C C_loop : Stmt α} {σ σ'' σ' : State α}
  (hrest : BigStep C_loop σ σ'')
  (eqC : C_loop = Stmt.loop C)
  (hbody : BigStep C σ'' σ') :
    BigStep (Stmt.loop C) σ σ' :=
    by
    induction hrest
    repeat' grind

lemma sem_iter_one {α : Type} (C : Stmt α) (S : Set (State α)) (n : ℕ) :
  Nat.iterate (sem C) n S ⊆ sem (Stmt.loop C) S := by
  induction n with
  | zero =>
    simp [Nat.iterate]
    grind
  | succ n ih =>
  {
    simp [Nat.iterate]
    have h : (sem C)^[n] (sem C S) = sem C ((sem C)^[n] S) := by
      exact Function.iterate_succ_apply' (sem C) n S
    rw [h]
    apply subsetI
    intro σ' hin
    apply in_semI
    have hex := in_semE hin
    rcases hex with ⟨σ'', in_S, step_C⟩
    have hloop : sem C.loop S σ'' :=
      by grind
    have hloop := in_semE hloop
    rcases hloop with ⟨σ, in_S_loop, step_loop⟩
    apply Exists.intro σ
    apply And.intro
    ·assumption
    exact BigStep.loop_more_symm step_loop rfl step_C
  }


lemma in_loop_then_iter {α : Type} {C C_loop : Stmt α} {S : Set (State α)} {σ σ' : State α}
  (hin : S σ)
  (heq : C_loop = Stmt.loop C)
  (h_trans : ⟨C_loop, σ⟩ ⟹ σ') :
   ∃ n, Nat.iterate (sem C) n S σ' :=
  by
    induction h_trans generalizing S with
    | loop_exit _ =>
      apply Exists.intro 0
      aesop
    | loop_more C0 σ1 σ2 σ3 step_one step_loop x5 ih =>
      clear x5
      cases heq
      have hin2 : sem C S σ2 := by grind
      specialize ih hin2
      simp at ih
      rcases ih with ⟨n, hin⟩
      apply Exists.intro (n + 1)
      have hconc : (sem C)^[n] (sem C S) = (sem C)^[n + 1] S := by
        exact rfl
      rw [hconc] at hin
      exact hin
    | _ => contradiction

@[simp]
lemma sem_iter {α : Type} (C : Stmt α) (S : Set (State α)) :
    sem (Stmt.loop C) S = ⋃ n : ℕ, Nat.iterate (sem C) n S := by
  apply Set.ext
  intro σ'
  apply Iff.intro
  {
    intro h
    have h := in_semE h
    rcases h with ⟨σ, in_S, step⟩
    have hn := in_loop_then_iter in_S rfl step
    rcases hn with ⟨n, in_iter_n⟩
    aesop
  }
  intro h
  have hn : ∃ n : ℕ, Nat.iterate (sem C) n S σ' :=
    by
    aesop
  rcases hn with ⟨n, in_iter_n⟩
  have hh := sem_iter_one C S n
  aesop

@[grind =]
lemma in_inter_iff {α : Type} (S₁ S₂ : Set (State α)) (σ' : State α) :
    (S₁ ∩ S₂) σ' ↔ S₁ σ' ∧ S₂ σ' :=
  by
  aesop

@[grind]
def to_bprop {α : Type} (b : BExp α) : State α → Prop :=
  fun σ => b σ = true

@[simp]
lemma sem_assume {α : Type} (b : BExp α) (S : Set (State α)) :
    sem (Stmt.assume b) S = S ∩ to_bprop b :=
    by
      apply funext
      grind

@[simp]
lemma in_indexed_union {α β : Type} (f : β → Set (State α)) (σ' : State α) :
    (⋃ x, f x) σ' ↔ ∃ x, f x σ' :=
    Set.mem_iUnion

@[simp]
lemma sem_indexed_union {α β : Type} (C : Stmt α) (f : β → Set (State α)) :
    sem C (⋃ x, f x) = ⋃ x, sem C (f x) := by
  apply funext
  intro σ'
  simp
  apply Iff.intro
  {
    intro h
    have h := in_semE h
    rcases h with ⟨σ, hin, step⟩
    simp at hin
    grind
  }
  {
    intro h
    rcases h with ⟨x, σ, hin, step⟩
    apply in_semI
    aesop
  }

@[simp]
lemma sem_assign {α : Type} (S : Set (State α)) (x : Var) (e : Exp α) :
  sem (Stmt.assign x e) S =  {σ' | ∃σ, S σ ∧ σ' = σ[x ↦ e σ]} :=
  by
    apply funext
    intro σ'
    simp [sem]
    grind
