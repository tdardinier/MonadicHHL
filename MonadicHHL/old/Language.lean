import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | S, f => {b | ∃a, a ∈ S ∧ b ∈ f a}

instance Set.Monad : Monad Set where
  pure := Set.pure
  bind := Set.bind

instance Set.LawfulMonad : LawfulMonad Set :=
  {
    pure_bind  :=
      by
        intro α β a f
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
    bind_pure_comp  :=
      by
        intro α ma
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
        sorry
    bind_assoc :=
      by
        intro α β γ f g ma
        simp [Bind.bind, Set.bind]
        apply Set.ext
        aesop
    seqLeft_eq := sorry
    seqRight_eq := sorry
    pure_seq := sorry
    bind_map := sorry }


abbrev generic_HHL_monad (α : Type) : Type → Type :=
  StateT α Set

abbrev generic_Hypra_monad (α : Type) : Type → Type :=
  OptionT (StateT α Set)

lemma Hypra_monad_simpler (α val : Type) :
  generic_Hypra_monad α val = (α → Set (Option val × α)) := by
    simp [generic_Hypra_monad, OptionT, StateT]

abbrev Var : Type :=
  String

def State (α : Type) : Type :=
  Var → α

abbrev HypraM (α val : Type) : Type :=
  -- State α → Set (Option α × State α)
  OptionT (StateT (State α) Set) val

lemma simpler_HypraM (α val : Type) :
  HypraM α val = (State α → Set (Option val × State α)) := by
    simp [HypraM, OptionT, StateT]

abbrev SuperHypraM (α val lval : Type) : Type :=
  -- State α → Set (Option α × State α)
  OptionT (StateT (State lval) (StateT (State α) Set)) val

lemma simpler_super_HypraM (α val lval : Type) :
  SuperHypraM α val lval = (State lval → State α → Set ((Option val × State lval) × State α)) := by
    simp [SuperHypraM, OptionT, StateT]

-- Goal: With divergence, where we keep only the logical variables
abbrev withDivergence (α val lval : Type) : Type :=
  OptionT (StateT (State α) (OptionT (StateT (State lval) Set))) val

--
lemma simpler_withDivergence (α val lval : Type) :
  withDivergence α val lval
  = (State α → State lval → Set (Option (Option val × State α) × State lval))
  := by
    simp [withDivergence, OptionT, StateT]








-- Goal


-- return, lit
def HypraM.pure {α val : Type} (v : val) : HypraM α val
  | σ => {(some v, σ)}

def rel_with
  {α val0 val1 : Type}
  (C : val0 → HypraM α val1)
  (p : Option val0 × State α)
  (p' : Option val1 × State α)
   : Prop :=
  match p with
  | (none, σ) => p' = (none, σ)
  | (some v, σ) => p' ∈ C v σ

-- bind, seq
def HypraM.bind {α val1 val2 : Type} (C₁ : HypraM α val1) (C₂ : val1 → HypraM α val2)
  : HypraM α val2 :=
  fun σ => { y | ∃ x ∈ C₁ σ, rel_with C₂ x y}

instance HypraM.Monad {α : Type} : Monad (HypraM α) where
  pure := HypraM.pure
  bind := HypraM.bind

instance HypraM.LawfulMonad {α : Type} : LawfulMonad (HypraM α) :=
  {
    pure_bind  :=
      by
        intro val1 val2 a f
        simp [Bind.bind, Pure.pure]
        apply funext
        intro x
        simp [HypraM.bind, HypraM.pure, rel_with]
    bind_pure_comp  :=
      sorry
    bind_assoc := sorry
    seqLeft_eq := sorry
    seqRight_eq := sorry
    pure_seq := sorry
    bind_map := sorry }

def semify {α val0 val1 : Type} (C : val0 → HypraM α val1) :
  Set (Option val0 × State α) → Set (Option val1 × State α)
  | S => { p' | ∃ p ∈ S, rel_with C p p'}

abbrev hyperassertion (α val : Type) : Type
:= Set (Option val × State α) → Prop

def triple {α val1 val2 : Type}
  (P : hyperassertion α val1)
  (C : val1 → HypraM α val2)
  (Q : hyperassertion α val2)
:=
  ∀ S, P S → Q (semify C S)


---- HHL triples

abbrev HHLM (α val : Type) : Type :=
  -- State α → Set (Option α × State α)
  StateT (State α) Set val

lemma simpler_HHLM (α val : Type) :
  HHLM α val = (State α → Set (val × State α)) := by
    simp [HHLM, StateT]

-- return, lit
def HHLM.pure {α val : Type} (v : val) : HHLM α val
  | σ => { (v, σ) }

def HHLM.rel_with
  {α val0 val1 : Type}
  (C : val0 → HHLM α val1)
  (p : val0 × State α)
  (p' : val1 × State α)
   : Prop :=
  p' ∈ C p.1 p.2

-- bind, seq
def HHLM.bind {α val1 val2 : Type} (C₁ : HHLM α val1) (C₂ : val1 → HHLM α val2)
  : HHLM α val2 :=
  fun σ => { y | ∃ x ∈ C₁ σ, HHLM.rel_with C₂ x y}

instance HHLM.Monad {α : Type} : Monad (HHLM α) where
  pure := HHLM.pure
  bind := HHLM.bind

def HHLM.semify {α val0 val1 : Type} (C : val0 → HHLM α val1) :
  Set (val0 × State α) → Set (val1 × State α)
  | S => { p' | ∃ p ∈ S, HHLM.rel_with C p p'}

abbrev HHLM.hyperassertion (α val : Type) : Type
:= Set (val × State α) → Prop

def HHLM.triple {α val1 val2 : Type}
  (P : HHLM.hyperassertion α val1)
  (C : val1 → HHLM α val2)
  (Q : HHLM.hyperassertion α val2)
:=
  ∀ S, P S → Q (HHLM.semify C S)


------ Connection between HypraM and HHLM

def lift_state_to_Hypra {α val : Type}
  (σ : val × State α) : Option val × State α :=
  (some σ.1, σ.2)

def lift_set_to_Hypra {α val : Type}
  (S : Set (val × State α)) : Set (Option val × State α) :=
  Set.image lift_state_to_Hypra S

def lift_to_Hypra {α val0 val1 : Type}
  (C : val0 → HHLM α val1) (v : val0) : HypraM α val1 :=
  fun σ => lift_set_to_Hypra (C v σ)

lemma rel_with_Hypra_HHL
  {α val0 val1 : Type}
  (C : val0 → HHLM α val1)
  (p : val0 × State α)
  (p' : val1 × State α) :
  rel_with (lift_to_Hypra C) (lift_state_to_Hypra p) (lift_state_to_Hypra p') ↔
    HHLM.rel_with C p p' := by
    simp [rel_with, HHLM.rel_with, lift_state_to_Hypra, lift_to_Hypra, lift_set_to_Hypra]


abbrev ext_state (α val : Type) : Type :=
  Option val × State α

-- attribute [-simp] Prod.exists
def err_set {α val1 val2 : Type} (S : Set (ext_state α val1)) : Set (ext_state α val2) :=
  { p | ∃ s ∈ S, p.1 = none ∧ p.2 = s.2 ∧ s.1 = none }

def some_set {α val : Type}
-- (f : ext_state α val → ext_state α val)
  (S : Set (ext_state α val)) : Set (val × State α) :=
  { (v, σ) | (some v, σ) ∈ S }


lemma Hypra_state_two_options
  {α val : Type}
  (x : ext_state α val) :
  (x.1 = none ∨ (∃ y, x = lift_state_to_Hypra y))
  := by
    rcases x with ⟨v, σ⟩
    cases v
    · simp
    rename_i v
    apply Or.inr
    apply Exists.intro (v, σ)
    simp [lift_state_to_Hypra]

lemma rel_with_arbitrary_pairs
  {α val0 val1 : Type}
  (C : val0 → HHLM α val1)
  (p : ext_state α val0)
  (p' : ext_state α val1) :
  rel_with (lift_to_Hypra C) p p'
  ↔ (p.1 = none ∧ p'.1 = none ∧ p.2 = p'.2) ∨
    (∃ v v', HHLM.rel_with C (v, p.2) (v', p'.2) ∧ p.1 = some v ∧ p'.1 = some v')
  := by
    simp [rel_with, HHLM.rel_with, lift_state_to_Hypra, lift_to_Hypra, lift_set_to_Hypra]
    rcases p with ⟨v, σ⟩
    cases v
    {
      simp
      aesop
    }
    simp
    aesop


lemma semify_Hypra_HHL
  {α val0 val1 : Type}
  (C : val0 → HHLM α val1)
  (S : Set (val0 × State α))
  :
  semify (lift_to_Hypra C) (lift_set_to_Hypra S)
  = Set.image lift_state_to_Hypra (HHLM.semify C S)
  := by
    simp [semify, HHLM.semify, lift_set_to_Hypra, lift_state_to_Hypra, Set.image, -Prod.exists]
    have h := rel_with_arbitrary_pairs C
    aesop

lemma relating_full_semify
  {α val0 val1 : Type}
  (C : val0 → HHLM α val1)
  (S : Set (ext_state α val0)) :
  semify (lift_to_Hypra C) S
  = lift_set_to_Hypra (HHLM.semify C (some_set S)) ∪ err_set S
  := by
    simp [semify, HHLM.semify, lift_set_to_Hypra, lift_state_to_Hypra,
      Set.image, err_set, some_set, -Prod.exists]
    have h := rel_with_arbitrary_pairs C
    aesop

lemma lift_to_triple_specialized
  {α val0 val1 : Type}
  (C : val0 → HHLM α val1)
  (P : hyperassertion α val1) :
  triple (fun S => P (lift_set_to_Hypra (HHLM.semify C (some_set S)) ∪ err_set S))
    (lift_to_Hypra C) P
:= by
  simp [triple]
  intro S hpre
  rw [relating_full_semify]
  assumption









--- Some lemmas


lemma rel_with_none_then_none
  {α val0 val1 : Type}
  {C : val0 → HypraM α val1}
  {p1 : Option val1 × State α}
  {σ : State α}
  (h : rel_with C (none, σ) p1) :
  p1 = (none, σ) := by
  rw [h]

lemma rel_with_trans
  {α val0 val1 val2 : Type}
  {C₁ : val0 → HypraM α val1}
  {C₂ : val1 → HypraM α val2}
  {p0 : Option val0 × State α}
  {p1 : Option val1 × State α}
  {p2 : Option val2 × State α}
  (h1 : rel_with C₁ p0 p1)
  (h2 : rel_with C₂ p1 p2) :
  rel_with (fun v0 => C₁ v0 >>=  C₂) p0 p2 := by
  simp [rel_with, Bind.bind, HypraM.bind]
  rcases p0 with ⟨v0, σ0⟩
  cases v0
  {
    simp
    have h := rel_with_none_then_none h1
    rw [h] at h2
    apply rel_with_none_then_none h2
  }
  simp
  rw [rel_with] at h1
  apply Exists.intro p1.1
  apply Exists.intro p1.2
  simp [h1]
  simp [rel_with] at h2
  exact h2

lemma rel_with_trans_rev
  {α val0 val1 val2 : Type}
  {C₁ : val0 → HypraM α val1}
  {C₂ : val1 → HypraM α val2}
  {p0 : Option val0 × State α}
  {p2 : Option val2 × State α}
  (hrel : rel_with (fun v0 => C₁ v0 >>= C₂) p0 p2) :
  ∃ p1 : Option val1 × State α,
    rel_with C₁ p0 p1 ∧ rel_with C₂ p1 p2 := by
  simp [rel_with]
  simp [rel_with, Bind.bind, HypraM.bind] at hrel
  rcases p0 with ⟨v0, σ0⟩
  cases v0
  {
    simp
    simp [hrel]
  }
  simp
  simp at hrel
  exact hrel

lemma semify_bind
  {α val0 val1 val2 : Type}
  (C₁ : val0 → HypraM α val1)
  (C₂ : val1 → HypraM α val2) :
  semify (fun v0 => C₁ v0 >>=  C₂) = semify C₂ ∘ semify C₁ :=
  by
    apply funext
    intro S
    simp [semify]
    apply Set.ext
    intro p2
    simp
    apply Iff.intro
    {
      intro h
      rcases h with ⟨v0, σ0, hrel⟩
      rcases hrel with ⟨hS, hrel⟩
      have h := rel_with_trans_rev hrel
      aesop
    }
    {
      intro h
      rcases h with ⟨v1, σ1, hrel⟩
      rcases hrel with ⟨⟨v0, σ0, hS, hrel1⟩, hrel2⟩
      apply Exists.intro v0
      apply Exists.intro σ0
      simp [hS]
      exact rel_with_trans hrel1 hrel2
    }


----------------------------------------------------------------------
-------------------------- Language constructs -----------------------
----------------------------------------------------------------------

-- read variable
def HypraM.read_var {α : Type} (x : Var) : HypraM α α
  | σ => {(some (σ x), σ)}

/-
def Hypra_read_var {α val : Type} (x : Var) : Set (Option val × (Var → val)) :=
  { (some (σ x), σ) | σ : Var → val }
-/

def BExp (α : Type) : Type :=
  State α → Bool

def HypraM.evalBExp {α : Type} (b : BExp α) : HypraM α Bool
  | σ => {(some (b σ), σ)}

def Exp (α β : Type) : Type :=
  State α → β

def HypraM.evalExp {α val : Type} (b : Exp α val) : HypraM α val
  | σ => {(some (b σ), σ)}

def update {var val : Type} [DecidableEq var] (f : var → val) (x : var) (v : val) : var → val :=
  fun y => if x = y then v else f y

notation:max s "[" x " ↦ " v "]" => update s x v

-- write variable with expression
def HypraM.write_var {α : Type} (x : Var) (e : Exp α α) : HypraM α Unit
  | σ => {(some (), σ[x ↦ e σ])}

-- assume
def HypraM.assume {α : Type} (b : BExp α) : HypraM α Unit
  | σ => if b σ then {(some (), σ)} else ∅

-- assert
def HypraM.assert {α : Type} (b : BExp α) : HypraM α Unit
  | σ => if b σ then {(some (), σ)} else {(none, σ)}

-- havoc variable
def HypraM.havoc {α : Type} (x : Var) : HypraM α Unit
  | σ => {(some (), σ[x ↦ v]) | v : α}

-- branch and if
def HypraM.branch {α val : Type} (C₁ C₂ : HypraM α val) : HypraM α val
  | σ => C₁ σ ∪ C₂ σ




-- HypraM α val = (State α → Set (Option val × State α)) := by
def HypraM.loop {α val : Type} (C : val → HypraM α val) (v : val) : HypraM α val
  | σ => ⋃ n : ℕ, Nat.iterate (semify C) n { (some v, σ) }

/-
def HypraM.if_then_else {α val : Type} (b : BExp α)
    (C₁ C₂ : HypraM α val) : HypraM α val :=
  fun σ =>
    if b σ then C₁ σ else C₂ σ
-/

def HypraM.if_then_else {α val : Type}
    (b : BExp α) (C₁ C₂ : HypraM α val) : HypraM α val :=
  do
    if ← HypraM.evalBExp b then
      C₁
    else
      C₂
/-
Sugar for:
do
  let cond ← HypraM.evalBExp b
  if cond then C₁ else C₂
-/


def LNot {α : Type} (b : BExp α) : BExp α :=
  fun σ => ¬b σ

lemma if_then_else_same_as_branch_assume {α val : Type} (b : BExp α)
    (C₁ C₂ : HypraM α val) :
  (do
    if ← HypraM.evalBExp b then C₁
    else C₂)
    =
    HypraM.branch
      (do HypraM.assume b; C₁)
      (do HypraM.assume (LNot b); C₂) :=
by
  apply funext
  intro x
  simp [HypraM.branch, Bind.bind, HypraM.bind, HypraM.assume, LNot, HypraM.evalBExp, rel_with]
  aesop

def increment_until (x : Var) (limit : Nat) : HypraM Nat Unit :=
  do
    while ← HypraM.evalBExp (fun σ => σ x < limit) do
      do
        HypraM.write_var x (fun σ => σ x + 1)


partial def HypraM.whileB_desugared {α}
    (b : BExp α) (C : HypraM α Unit) : HypraM α Unit :=
  let rec loop :=
    do
      let cond ← HypraM.evalBExp b
      if cond then
        C
        loop
      else
        pure ()
  loop

def HypraM.whileB {α} (b : BExp α) (C : HypraM α Unit) : HypraM α Unit :=
  do
    while ← HypraM.evalBExp b do
      C

-- assume
def HHLM.assume {α : Type} (b : BExp α) : HHLM α Unit
  | σ => if b σ then {((), σ)} else ∅


@[simp]
lemma assume_lifted {α val : Type} (b : BExp α) :
  lift_to_Hypra (fun (_ : val) => HHLM.assume b) = (fun _ => HypraM.assume b) := by
    apply funext
    intro v
    apply funext
    intro σ
    simp [lift_to_Hypra, lift_set_to_Hypra, HHLM.assume, HypraM.assume, Set.image, -Prod.exists]
    aesop

-----------------------------------------------------
------------------------ Rules ----------------------
-----------------------------------------------------

lemma rule_seq
  {α val0 val1 val2 : Type}
  {P : hyperassertion α val0}
  {R : hyperassertion α val1}
  {Q : hyperassertion α val2}
  {C₁ : val0 → HypraM α val1}
  {C₂ : val1 → HypraM α val2}
  (h1 : triple P C₁ R)
  (h2 : triple R C₂ Q) :
  triple P (fun v0 => C₁ v0 >>= C₂) Q
  := by
    simp [triple]
    intro S hpre
    simp [semify_bind]
    rw [triple] at h1 h2
    aesop

lemma HHLM.semify_assume
  {α : Type}
  (b : BExp α)
  (S : Set (Unit × State α)) :
  HHLM.semify (fun _ ↦ HHLM.assume b) S = { p | p ∈ S ∧ b p.2 = true }
  := by
    apply Set.ext
    intro σ
    simp [HHLM.semify, rel_with, assume]

lemma HypraM.rule_assume
  {α : Type}
  (b : BExp α)
  (P : hyperassertion α Unit) :
  triple
    (fun S => P (lift_set_to_Hypra ({ p | p ∈ some_set S ∧ b p.2 = true }) ∪ err_set S))
    (fun _ => HypraM.assume b)
    P
  := by
  have h := lift_to_triple_specialized (fun (_ : Unit) => HHLM.assume b) P
  simp at h
  have heq : ∀ S, HHLM.semify (fun x ↦ HHLM.assume b) (some_set S)
                = {p | p ∈ some_set S ∧ b p.2 = true}
    := by simp [HHLM.semify_assume]
  aesop


/-
abbrev HypraM (α val : Type) : Type :=
  -- State α → Set (Option α × State α)
  OptionT (StateT (State α) Set) val

lemma simpler_HypraM (α val : Type) :
  HypraM α val = (State α → Set (Option val × State α)) := by
    simp [HypraM, OptionT, StateT]
-/


@[grind]
def to_bprop {α : Type} (b : BExp α) : State α → Prop :=
  fun σ => b σ = true

lemma rule_cons
  {α val1 val2 : Type}
  {P P' : hyperassertion α val1}
  {Q Q' : hyperassertion α val2}
  {C : val1 → HypraM α val2}
  (htriple : triple P' C Q')
  (hcons_pre : ∀ S, P S → P' S)
  (hcons_post : ∀ S, Q' S → Q S) :
  triple P C Q
  := by
    simp [triple]
    intro S hpre
    apply hcons_post
    apply htriple
    apply hcons_pre
    exact hpre

lemma rule_cons_pre
  {α val1 val2 : Type}
  {P P' : hyperassertion α val1}
  {Q : hyperassertion α val2}
  {C : val1 → HypraM α val2}
  (htriple : triple P' C Q)
  (hcons_pre : ∀ S, P S → P' S) :
  triple P C Q
  := by
    simp [triple]
    intro S hpre
    apply htriple
    apply hcons_pre
    exact hpre

lemma not_none_unit
  (p : Option Unit)
  (h : p ≠ none) :
  p = some () := by
    cases p
    {
      contradiction
    }
    simp


lemma rel_with_assume
  {α val : Type}
  (b : BExp α)
  (p : ext_state α val)
  (p' : ext_state α Unit) :
  rel_with (fun _ ↦ HypraM.assume b) p p' ↔
  ((p.1 = none ∧ p'.1 = none ∧ p.2 = p'.2)) ∨
  (p.1 ≠ none ∧ p'.1 ≠ none ∧ p.2 = p'.2 ∧ b p.2 = true)
  := by
    simp [rel_with, HypraM.assume]
    rcases p with ⟨v, σ⟩
    cases v
    {
      simp
      aesop
    }
    simp
    have h := not_none_unit p'.1
    aesop

lemma rule_from_rel_with
  {α val1 val2 : Type}
  (C : val1 → HypraM α val2)
  (P : hyperassertion α val2)
  :
  triple (fun S => P {p' | ∃ p ∈ S, rel_with (fun v ↦ C v) p p' }) C P
  := by
    simp [triple, semify]

lemma rule_from_rel_withI
  {α val1 val2 : Type}
  (C : val1 → HypraM α val2)
  (P : hyperassertion α val1)
  (Q : hyperassertion α val2)
  (h : ∀ S, P S → Q {p' | ∃ p ∈ S, rel_with C p p' })
  :
  triple P C Q
  := rule_cons_pre (rule_from_rel_with C Q) h



lemma set_union_disj_same {α : Type} (P Q D : α → Prop)
  (h : ∀ x, P x ∨ Q x ↔ D x) :
  { σ | P σ } ∪ { σ | Q σ } = { σ | D σ } := by
    apply Set.ext
    intro σ
    simp [h]

lemma rel_with_err_set_same {α val0 val1 : Type}
  (C : val0 → HypraM α val1)
  (S : Set (ext_state α val0)) :
  {p' | ∃ v σ, (some v, σ) ∈ S ∧ p' ∈ C v σ} ∪ err_set S
    = {p' | ∃ p ∈ S, rel_with C p p'}
  := by
    apply set_union_disj_same
    intro p'
    simp [rel_with]
    grind

lemma semify_simpler_def {α val0 val1 : Type}
  (C : val0 → HypraM α val1)
  (S : Set (ext_state α val0)) :
  semify C S
  = {p' | ∃ v σ, (some v, σ) ∈ S ∧ p' ∈ C v σ} ∪ err_set S
  := by
    simp [semify, rel_with_err_set_same C S]

lemma generic_triple_from_semantics
  {α val0 val1 : Type}
  (C : val0 → HypraM α val1)
  (P : hyperassertion α val1) :
  triple
    (fun S => P ( { p' | ∃v σ, (some v, σ) ∈ S ∧ p' ∈ C v σ} ∪ err_set S))
    C
    P
:= by
  apply rule_from_rel_withI
  intro S hpre
  have heq := rel_with_err_set_same C S
  aesop

/-
{p' | ∃ v σ, (some v, σ) ∈ S ∧ p' ∈ C v σ} ∪ err_set S)
⊢ P {p' | ∃ p ∈ S, rel_with C p p'}
-/


lemma rule_assume
  {α val : Type}
  (P : hyperassertion α Unit)
  (b : BExp α)
  :
  triple (fun S => P { p | p ∈ S ∧ (p.1 = none ∨ (b p.2 = true)) }) (fun _ => HypraM.assume b) P
  := by
    apply rule_from_rel_withI
    simp [rel_with_assume, -Prod.exists]
    intro S
    have h : {x | x ∈ S ∧ x.1 = none} ∪ {x | x ∈ S ∧ b x.2 = true}
    = {p' | ∃ p ∈ S, p.1 = none ∧ p'.1 = none ∧ p.2 = p'.2 ∨ ¬p.1 = none ∧ ¬p'.1 = none ∧ p.2 = p'.2 ∧ b p.2 = true}
      := by
      apply set_union_disj_same
      intro x
      apply Iff.intro
      {
        intro h
        apply Exists.intro x
        have hem := Classical.em (x.1 = none)
        aesop
      }
      {
        intro h
        rcases h with ⟨p, hpS, hcase⟩
        have heq : x = p := by
          cases x; cases p; simp
          sorry
        simp [heq]
        aesop
      }
    simp [h]

lemma rel_with_write_var
  {α : Type}
  (x : Var)
  (e : Exp α α)
  (p p' : ext_state α Unit) :
  rel_with (fun _ ↦ HypraM.write_var x e) p p' ↔ (p.1 = none ∧ p = p') ∨
    (p.1 ≠ none ∧ p'.1 = some () ∧ p'.2 = p.2[x ↦ e p.2])
  := by
    simp [rel_with, HypraM.write_var]
    aesop

lemma rule_assign
  {α : Type}
  (P : hyperassertion α Unit)
  (x : Var)
  (e : Exp α α)
  :
  triple (fun S => P (err_set S ∪ (fun p => (some (), p.2[x ↦ e p.2])) '' (some_set S)))
    (fun (_ : Unit) => HypraM.write_var x e) P
  := by
    apply rule_from_rel_withI
    simp [rel_with_write_var, -Prod.exists]
    intro S
    have heq :
      {p | p ∈ S ∧ p.1 = none} ∪ {p' | ∃ p ∈ S, ¬p.1 = none ∧ p' = (some (), p.2[x ↦ e p.2])}
      = {p' | ∃ p ∈ S, p.1 = none ∧ p = p' ∨ ¬p.1 = none ∧ p'.1 = some () ∧ p'.2 = p.2[x ↦ e p.2]}
    := by aesop
    have new_eq :
      err_set S ∪ {x_1 | ∃ a b, (a, b) ∈ some_set S ∧ (some (), b[x ↦ e b]) = x_1}
      = {p' | ∃ a b, (a, b) ∈ S ∧ (a = none ∧ (a, b) = p' ∨ ¬a = none ∧ p'.1 = some () ∧ p'.2 = b[x ↦ e b])}
    := by
      simp [some_set, err_set]
      apply Set.ext
      intro x
      simp
      sorry
    simp [Set.image, -Prod.exists]
    aesop

def join {α val : Type}
  (P Q : hyperassertion α val) : hyperassertion α val :=
  fun S => ∃ S₁ S₂, S = S₁ ∪ S₂ ∧ P S₁ ∧ Q S₂

lemma semify_branch_union {α val1 val2 : Type}
  (C₁ C₂ : val1 → HypraM α val2)
  (S : Set (Option val1 × State α)) :
  semify (fun v => HypraM.branch (C₁ v) (C₂ v)) S
  = semify C₁ S ∪ semify C₂ S
  := by
    simp [semify_simpler_def]
    have heq : {p' | ∃ v σ, (some v, σ) ∈ S ∧ p' ∈ (C₁ v).branch (C₂ v) σ}
    = {p' | ∃ v σ, (some v, σ) ∈ S ∧ p' ∈ C₁ v σ} ∪ {p' | ∃ v σ, (some v, σ) ∈ S ∧ p' ∈ C₂ v σ}
      := by
        apply Set.ext
        intro p'
        simp [HypraM.branch]
        aesop
    aesop

lemma rule_branch {α val1 val2 : Type}
  {P : hyperassertion α val1}
  {Q₁ Q₂ : hyperassertion α val2}
  {C₁ : val1 → HypraM α val2}
  {C₂ : val1 → HypraM α val2}
  (h1 : triple P C₁ Q₁)
  (h2 : triple P C₂ Q₂) :
  triple P (fun v0 => HypraM.branch (C₁ v0) (C₂ v0)) (join Q₁ Q₂)
  := by
    simp [triple, join, semify_branch_union]
    aesop

lemma iterate_mono {α : Type}
  (f : Set α → Set α)
  (S S' : Set α)
  (n : Nat)
  (hmono : ∀ S S', S ⊆ S' → f S ⊆ f S')
  (hsub : S ⊆ S') :
  (f^[n] S ⊆ f^[n] S') := by
    induction n generalizing S S' with
    | zero =>
      simp [Nat.iterate]
      exact hsub
    | succ n ih =>
      simp [Nat.iterate]
      aesop

lemma semify_mono {α val0 val1 : Type}
  (C : val0 → HypraM α val1)
  (S S' : Set (Option val0 × State α))
  (hsub : S ⊆ S') :
  semify C S ⊆ semify C S' := by
    simp [semify]
    aesop

lemma in_iterate_then_elem {α val : Type}
  (i : Nat)
  (C : val → HypraM α val)
  (p' : Option val × State α)
  (S : Set (Option val × State α))
  (hin : p' ∈ (semify C)^[i] S) :
  ∃ p ∈ S, p' ∈ (semify C)^[i] {p}
:= by
  induction i generalizing S p' with
  | zero =>
    simp [Nat.iterate] at hin
    aesop
  | succ i ih =>
    simp [Nat.iterate] at hin
    -- simp [Nat.iterate, -Prod.exists]
    specialize ih p' (semify C S) hin
    rcases ih with ⟨p'', hp'', hin⟩
    simp [semify, -Prod.exists] at hp''
    rcases hp'' with ⟨p, hS, hrel⟩
    apply Exists.intro p
    apply And.intro hS
    simp [Nat.iterate]
    have hmono := iterate_mono (semify C) {p''} (semify C {p}) i
    specialize hmono (semify_mono C)
    specialize hmono (by
      simp [semify]
      exact hrel
    )
    aesop

lemma semify_none {α val : Type}
  (C : val → HypraM α val)
  (i : Nat)
  (σ : State α) :
  (semify C)^[i] {(none, σ)} = {(none, σ)} := by
    induction i with
    | zero =>
      simp [Nat.iterate]
    | succ i ih =>
      simp [Nat.iterate]
      simp [semify, rel_with]
      simp [ih]

lemma semify_iter {α val : Type}
  (C : val → HypraM α val)
  (S : Set (Option val × State α)) :
  semify (HypraM.loop C) S
  = ⋃ n : ℕ, Nat.iterate (semify C) n S
  := by
    apply Set.ext
    intro p'
    simp [semify, rel_with, HypraM.loop]
    apply Iff.intro
    {
      intro h
      rcases h with ⟨v, σ, hS, h⟩
      cases v
      {
        simp at h
        apply Exists.intro 0
        aesop
      }
      {
        rename_i v
        simp at h
        rcases h with ⟨i, h⟩
        apply Exists.intro i
        have h : (semify C)^[i] {(some v, σ)} ⊆ (semify C)^[i] S := by
          apply iterate_mono (semify C) { (some v, σ) } S i
          · apply semify_mono
          aesop
        aesop
      }
    }
    {
      intro h
      rcases h with ⟨i, h⟩
      have hh := in_iterate_then_elem i C p' S h
      rcases hh with ⟨p, hpS, h⟩
      rcases p with ⟨v, σ⟩
      apply Exists.intro v
      apply Exists.intro σ
      apply And.intro hpS
      cases v
      {
        simp
        have hh := semify_none C i σ
        aesop
      }
      {
        simp
        aesop
      }
    }

def infinite_join {α val : Type}
  (I : Nat → hyperassertion α val) :
  hyperassertion α val :=
  fun S => ∃ f : Nat → Set (Option val × State α),
    (∀ n, I n (f n)) ∧ S = ⋃ n : ℕ, f n

theorem rule_iter {α val : Type}
  {I : Nat → hyperassertion α val}
  {C : val → HypraM α val}
  (hinv : ∀ n, triple (I n) C (I (n + 1))) :
  triple (I 0) (HypraM.loop C) (infinite_join I)
  := by
    simp [triple, semify_iter, infinite_join]
    intro S hpre
    apply Exists.intro (fun n => Nat.iterate (semify C) n S)
    apply And.intro
    {
      intro n
      induction n with
      | zero =>
        simp [Nat.iterate]
        exact hpre
      | succ n ih =>
        simp [Nat.iterate]
        have heq : (semify C)^[n] (semify C S) = semify C (Nat.iterate (semify C) n S) := by
          exact Function.iterate_succ_apply' (semify C) n S
        rw [heq]
        apply hinv
        exact ih
    }
    {
      simp
    }

-------------------------------------------------------
---------------- Unit specialization ------------------
-------------------------------------------------------

abbrev semify_unit {α : Type} (C : HypraM α Unit) :
  Set (Option Unit × State α) → Set (Option Unit × State α)
  := semify (fun _ => C)

def HypraM.loop_unit {α : Type} (C : HypraM α Unit) : HypraM α Unit
  --| σ => ⋃ n : ℕ, Nat.iterate (semify (fun _ => C)) n { (some (), σ) }
  := HypraM.loop (fun _ => C) ()


abbrev hyperassertion_unit (α : Type) : Type
:= Set (Option Unit × State α) → Prop

def triple_unit {α : Type}
  (P : hyperassertion_unit α)
  (C : HypraM α Unit)
  (Q : hyperassertion_unit α)
:=
  ∀ S, P S → Q (semify_unit C S)

lemma semify_bind_unit {α : Type}
  (C₁ C₂ : HypraM α Unit) :
 semify_unit (do C₁; C₂) = semify_unit C₂ ∘ semify_unit C₁
 := semify_bind (fun _ => C₁) (fun _ => C₂)

lemma rule_seq_unit {α : Type} {P R Q : hyperassertion_unit α} {C₁ C₂ : HypraM α Unit}
  (h1 : triple_unit P C₁ R) (h2 : triple_unit R C₂ Q) :
  triple_unit P (do C₁; C₂) Q
  := rule_seq h1 h2

abbrev ext_state_unit (α : Type) : Type :=
  ext_state α Unit

lemma rel_with_assume_unit {α : Type}
  (b : BExp α)
  (p p' : ext_state_unit α) :
  rel_with (fun _ ↦ HypraM.assume b) p p' ↔ (p = p' ∧ (p.1 = none ∨ (b p.2 = true)))
  := by
    simp [rel_with, HypraM.assume]
    aesop

lemma rule_cons_unit
  {α : Type}
  {P P' Q Q' : hyperassertion_unit α}
  {C : HypraM α Unit}
  (htriple : triple_unit P' C Q')
  (hcons_pre : ∀ S, P S → P' S)
  (hcons_post : ∀ S, Q' S → Q S) :
  triple_unit P C Q
  := rule_cons htriple hcons_pre hcons_post

lemma rule_cons_pre_unit
  {α : Type}
  {P P' Q : hyperassertion_unit α}
  {C : HypraM α Unit}
  (htriple : triple_unit P' C Q)
  (hcons_pre : ∀ S, P S → P' S) :
  triple_unit P C Q
  := rule_cons_unit htriple hcons_pre (by simp)

lemma rule_cons_post_unit
  {α : Type}
  {P Q Q' : hyperassertion_unit α}
  {C : HypraM α Unit}
  (htriple : triple_unit P C Q')
  (hcons_post : ∀ S, Q' S → Q S) :
  triple_unit P C Q
  := rule_cons_unit htriple (by simp) hcons_post

lemma rule_from_rel_with_unit
  {α : Type}
  (C : HypraM α Unit)
  (P : hyperassertion α Unit) :
  triple_unit (fun S => P {p' | ∃ p ∈ S, rel_with (fun _ ↦ C) p p' }) C P
  := rule_from_rel_with (fun _ => C) P


lemma rule_from_rel_with_unitI
  {α : Type}
  (C : HypraM α Unit)
  (P Q : hyperassertion α Unit)
  (h : ∀ S, P S → Q {p' | ∃ p ∈ S, rel_with (fun _ ↦ C) p p' })
  :
  triple_unit P C Q
  := rule_cons_pre_unit (rule_from_rel_with_unit C Q) h

lemma rule_assume_unit
  {α : Type}
  (P : hyperassertion α Unit)
  (b : BExp α)
  :
  triple_unit (fun S => P { p | p ∈ S ∧ (p.1 = none ∨ (b p.2 = true)) }) (HypraM.assume b) P
  := by
    apply rule_from_rel_withI
    simp [rel_with_assume, -Prod.exists]
    sorry

lemma rel_with_write_var_unit
  {α : Type}
  (x : Var)
  (e : Exp α α)
  (p p' : ext_state_unit α) :
  rel_with (fun _ ↦ HypraM.write_var x e) p p' ↔ (p.1 = none ∧ p = p') ∨
    (p.1 ≠ none ∧ p'.1 = some () ∧ p'.2 = p.2[x ↦ e p.2])
  := by
    simp [rel_with, HypraM.write_var]
    aesop

/-
lemma rule_assign_unit
  {α : Type}
  (P : hyperassertion α Unit)
  (x : Var)
  (e : Exp α α)
  :
  triple_unit (fun S => P (err_set S ∪ some_set (fun p => (some (), p.2[x ↦ e p.2])) S))
    (HypraM.write_var x e) P
  := by
    apply rule_from_rel_withI
    simp [rel_with_write_var, -Prod.exists]
    intro S
    have heq :
      {p | p ∈ S ∧ p.1 = none} ∪ {p' | ∃ p ∈ S, ¬p.1 = none ∧ p' = (some (), p.2[x ↦ e p.2])}
      = {p' | ∃ p ∈ S, p.1 = none ∧ p = p' ∨ ¬p.1 = none ∧ p'.1 = some () ∧ p'.2 = p.2[x ↦ e p.2]}
    := by aesop
    rw [heq]
    simp
-/

-------------------------------------------------
------------- Shallow syntactic rules -----------
-------------------------------------------------

def Hyper.ForallState (α val : Type)
    (P : ext_state α val → hyperassertion α val) : hyperassertion α val :=
  fun S => ∀ σ ∈ S, P σ S

def Hypra.ExistsState (α val : Type)
    (P : ext_state α val → hyperassertion α val) : hyperassertion α val :=
  fun S => ∃ σ ∈ S, P σ S
