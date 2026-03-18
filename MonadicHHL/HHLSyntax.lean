import MonadicHHL.HHLMonads

def H.type (M : Type _ → Type _) [Monad M] [HHL M] (α : Type _) : Type _ :=
  @HHL.hyperassertion M _ _ α

def H.pure {M : Type _ → Type _} [Monad M] [HHL M] {α : Type _} (P : Prop)
  : H.type M α :=
  fun _ => P

class HHLSyntax (M : Type _ → Type _) [Monad M] extends HHL M where
  -- Forall {α : Type _} (P : α → H.type M α) : H.type M α
  -- Exists {α : Type _} (P : α → H.type M α) : H.type M α
  -- Forall {α : Type _} (P : α → H.type M α) : H.type M α
  --ForallActive {α : Type _} (b : α → Prop) (P : elemType α → H.type M α) : H.type M α
  CheckElem {α : Type _} (b : α → Prop) (σ : elemType α) : Prop
  MapElem {α β : Type _} (f : α → β) (σ : elemType α) : elemType β

/-
def H.low {M : Type _ → Type _} [Monad M] [HHLSyntax M] {α β : Type _}
  (f : α → β) : H.type M α :=
  HHLSyntax.Forall M (fun σ₁ => HHLSyntax.Forall M (fun σ₂ => H.pure (f σ₁ = f σ₂)))
-/
instance : HHLSyntax Id where
  -- Forall P := fun S => ∀ σ ∈ S, P σ S
  -- ForallActive b P := fun S => ∀ σ ∈ S, b σ → P σ S
  CheckElem b σ := b σ
  MapElem f := f

instance : HHLSyntax Set where
  -- Forall P := fun S => ∀ σ ∈ S, P σ S
  -- ForallActive b P := fun S => ∀ σ ∈ S, b σ → P σ S
  CheckElem b σ := b σ
  MapElem f := f

instance (M : Type _ → Type _) [Monad M] [LawfulMonad M] [HHLSyntax M] : HHLSyntax (OptionT M) where
  /-
  Forall P := HHLSyntax.Forall
    (fun σ => match σ with
      | some a => P a
      | none   => H.pure True)
  -/
  CheckElem b := HHLSyntax.CheckElem (fun x => match x with
      | some a => b a
      | none   => False)
  MapElem f := HHLSyntax.MapElem (fun x => match x with
      | some a => some (f a)
      | none   => none)

def OptionT.isOk {α : Type _} {M : Type _ → Type _} [Monad M] [HHLSyntax M]
  : HHL.elemType M (Option α) → Prop :=
  HHLSyntax.CheckElem (fun x => Option.isSome x = true)

def OptionT.isErr {α : Type _} {M : Type _ → Type _} [Monad M] [HHLSyntax M]
  : HHL.elemType M (Option α) → Prop :=
  HHLSyntax.CheckElem (fun x => match x with
      | some _ => False
      | none   => True)

instance {σ : Type _} (M : Type _ → Type _) [Monad M] [LawfulMonad M] [HHLSyntax M]
  : HHLSyntax (StateT σ M) where
  -- Forall P := HHLSyntax.Forall (fun p => P p.1)
  CheckElem b := HHLSyntax.CheckElem (fun p => b p.1)
  MapElem f := HHLSyntax.MapElem (fun p => (f p.1, p.2))

-- Concrete cases

def Id.Forall {α : Type _} (P : α → H.type Id α) : H.type Id α :=
  fun S => ∀ v ∈ S, P v S

def Set.Forall {α : Type _} (P : α → H.type Set α) : H.type Set α :=
  fun S => ∀ v ∈ S, P v S

def OptionT.Id.ForallOk {α : Type _} (P : α → H.type (OptionT Id) α) : H.type (OptionT Id) α :=
  fun S => ∀ v ∈ S,
    match v with
    | some x => P x S
    | none   => True -- exists would be false

def OptionT.Set.ForallOk {α : Type _} (P : α → H.type (OptionT Set) α)
  : H.type (OptionT Set) α :=
  fun S => ∀ v ∈ S,
    match v with
    | some x => P x S
    | none   => True -- exists would be false

def OptionT.Id.ForallErr {α : Type _} (P : Unit → H.type (OptionT Id) α) : H.type (OptionT Id) α :=
  fun S => ∀ v ∈ S,
    match v with
    | some _ => True -- exists would be false
    | none   => P () S

def OptionT.Set.ForallErr {α : Type _} (P : Unit → H.type (OptionT Set) α)
  : H.type (OptionT Set) α :=
  fun S => ∀ v ∈ S,
    match v with
    | some _ => True -- exists would be false
    | none   => P () S

def StateT.Id.Forall {σ α : Type _} (P : α × σ → H.type (StateT σ Id) α)
  : H.type (StateT σ Id) α :=
  fun S => ∀ p ∈ S, P p S

def StateT.Set.Forall {σ α : Type _} (P : α × σ → H.type (StateT σ Id) α)
  : H.type (StateT σ Id) α :=
  fun S => ∀ p ∈ S, P p S

def OptionT.StateT.Id.ForallOk {σ α : Type _} (P : α × σ → H.type (OptionT (StateT σ Id)) α)
  : H.type (OptionT (StateT σ Id)) α :=
  fun S => ∀ p, p ∈ S → ∀ h : p.1.isSome, P (p.1.get h, p.2) S

def OptionT.StateT.Id.ForallErr {σ α : Type _} (P : Unit × σ → H.type (OptionT (StateT σ Id)) α)
  : H.type (OptionT (StateT σ Id)) α :=
  fun S => ∀ p ∈ S, p.1.isNone → P ((), p.2) S

-- How to turn x : ElemType M (Option α) into ElemType M α???
-- Need a map elemType?

-- How to write OptionT.StateT.Id.Forall with the combinators?
def OptionT.ForallErr {α : Type _} {M : Type _ → Type _} [Monad M] [HHLSyntax M] [LawfulMonad M]
  [Inhabited α]
  (P : HHL.elemType M Unit → H.type (OptionT M) α) : H.type (OptionT M) α :=
  (fun S =>
    ∀ p ∈ S, OptionT.isErr p →
    -- HHLSyntax.CheckElem (M := OptionT M) Option.isSome p →
      P (HHLSyntax.MapElem (fun _ => ()) p) S)

def OptionT.ForallOk {α : Type _} {M : Type _ → Type _} [Monad M] [HHLSyntax M] [LawfulMonad M]
  [Inhabited α]
  (P : HHL.elemType M α → H.type (OptionT M) α) : H.type (OptionT M) α :=
  (fun S =>
    ∀ p ∈ S, OptionT.isOk p →
      P (HHLSyntax.MapElem the p) S)

lemma forallOkState_same
  {σ α : Type _}
  [Inhabited α]
  (P : α × σ → H.type (OptionT (StateT σ Id)) α) :
  OptionT.StateT.Id.ForallOk P = OptionT.ForallOk P
:= by
  apply funext
  intro S
  simp [OptionT.StateT.Id.ForallOk, OptionT.ForallOk]
  simp [HHLSyntax.MapElem]
  simp [OptionT.isOk]
  simp [HHLSyntax.CheckElem, the, Option.getD]
  grind

lemma forallErrState_same
  {σ α : Type _}
  [Inhabited α]
  (P : Unit × σ → H.type (OptionT (StateT σ Id)) α) :
  OptionT.StateT.Id.ForallErr P = OptionT.ForallErr P
:= by
  apply funext
  intro S
  simp [OptionT.StateT.Id.ForallErr, OptionT.ForallErr]
  simp [HHLSyntax.MapElem]
  simp [OptionT.isErr]
  simp [HHLSyntax.CheckElem]
  grind



lemma forallOkId_same
  {α : Type _}
  [Inhabited α]
  (P : α → H.type (OptionT Id) α) :
  OptionT.Id.ForallOk P = OptionT.ForallOk P
:= by
  apply funext
  intro S
  simp [OptionT.Id.ForallOk, OptionT.ForallOk]
  simp [HHLSyntax.MapElem]
  simp [OptionT.isOk]
  simp [HHLSyntax.CheckElem, the, Option.getD]
  grind

lemma forallErrId_same
  {α : Type _}
  [Inhabited α]
  (P : Unit → H.type (OptionT Id) α) :
  OptionT.Id.ForallErr P = OptionT.ForallErr P
:= by
  apply funext
  intro S
  simp [OptionT.Id.ForallErr, OptionT.ForallErr]
  simp [HHLSyntax.MapElem]
  simp [OptionT.isErr]
  simp [HHLSyntax.CheckElem]
  grind

lemma forallOkSet_same
  {α : Type _}
  [Inhabited α]
  (P : α → H.type (OptionT Set) α) :
  OptionT.Set.ForallOk P = OptionT.ForallOk P
:= by
  apply funext
  intro S
  simp [OptionT.Set.ForallOk, OptionT.ForallOk]
  simp [HHLSyntax.MapElem]
  simp [OptionT.isOk]
  simp [HHLSyntax.CheckElem, the, Option.getD]
  grind

lemma forallErrSet_same
  {α : Type _}
  [Inhabited α]
  (P : Unit → H.type (OptionT Set) α) :
  OptionT.Set.ForallErr P = OptionT.ForallErr P
:= by
  apply funext
  intro S
  simp [OptionT.Set.ForallErr, OptionT.ForallErr]
  simp [HHLSyntax.MapElem]
  simp [OptionT.isErr]
  simp [HHLSyntax.CheckElem]
  grind



-- Let's pretend Option base is DivM

instance : HHL Option where
  elemType α := Option α
  relWith {α β : Type _} (C : α → Option β) (p : Option α) (p' : Option β) :=
    Option.bind p C = p'
  bind_rel C₁ C₂ p₀ p₂ := by
    simp [bind, Option.bind]
    aesop

instance : HHLSyntax Option where
  -- Forall P := fun S => ∀ σ ∈ S, P σ S
  CheckElem b σ :=
    match σ with
      | some a => b a
      | none   => False
  MapElem := Option.map


abbrev DivMonad σ := OptionT (StateT σ Option)

-- TODO

example (σ : Type) : HHL.elemType (DivMonad σ) α = Option (Option α × σ) := by
  simp [HHL.elemType]


def ForallNonTerm {σ : Type _} {α : Type _} [Inhabited α]
  (P : Unit → H.type (DivMonad σ) α) : H.type (DivMonad σ) α := fun S =>
    ∀ p ∈ S, if p.isNone then P () S else True

-- OptionT.ForallErr boils down Option (Unit × σ)
-- OptionT.ForallOk boils down Option (α × σ)
-- So need to check that it's some (otherwise it's clearly a NonTerm)

def ForallErr {σ : Type _} {α : Type _} [Inhabited α]
  (P : Unit × σ → H.type (DivMonad σ) α) : H.type (DivMonad σ) α := fun S =>
  sorry

/-

lemma forall_optionT_Id_equiv
  {α : Type _} (P : α → Prop) :
  @HHLSyntax.Forall (OptionT Id) _ _ _ (fun σ => H.pure (P σ))
  = (fun S => ∀ σ ∈ S, ∀ x, σ = Option.some x → P x) := by
    apply funext
    intro S
    simp [HHLSyntax.Forall]
    unfold H.pure
    apply Iff.intro
    {
      intro h σ hσ x heq
      specialize h (some x)
      aesop
    }
    {
      aesop
    }

def ForallState {σ : Type _} {M : Type _ → Type _} [Monad M] [HHLSyntax M] {α : Type _}
  (P : α × σ → H.type M (α × σ)) : H.type (StateT σ M) α :=
  @HHLSyntax.Forall M _ _ _ P

lemma equiv_forall_state {σ α : Type _}
  (P : α × σ → H.type Id (α × σ)) :
  ForallState P
  = (fun S => ∀ p ∈ S, P p S) := by
  rfl

abbrev StateOption (σ : Type _) : Type _ → Type _ := OptionT (StateT σ Id)

lemma equiv_forall_state_option {σ α : Type _}
  (P : α × σ → H.type (StateOption σ) α) :
  @ForallState σ (StateOption σ) _ _ _ P
  = sorry :=
  sorry

-/

/-
class HHL (M : Type _ → Type _) [Monad M] where
  elemType (α : Type _) : Type _
  relWith : {α β : Type _} → (α → M β) → elemType α → elemType β → Prop
  bind_rel
    {α₀ α₁ α₂ : Type _}
    (C₁ : α₀ → M α₁) (C₂ : α₁ → M α₂)
    (p₀ : elemType α₀) (p₂ : elemType α₂) :
      relWith (fun v₁ ↦ bind (C₁ v₁) C₂) p₀ p₂
      ↔ ∃ p₁, relWith C₁ p₀ p₁ ∧ relWith C₂ p₁ p₂
-/

def H.ForallActive {M : Type _ → Type _} [Monad M] [HHLSyntax M] {α : Type _}
  (b : α → Prop) (P : HHL.elemType M α → H.type M α) : H.type M α :=
  fun S => ∀ σ ∈ S, HHLSyntax.CheckElem b σ → P σ S

-- generic (kinda useless) forall?
def H.Forall {M : Type _ → Type _} [Monad M] [HHL M] {α : Type _}
  (P : HHL.elemType M α → H.type M α) : H.type M α :=
  fun S => ∀ σ ∈ S, P σ S

def H.Exists {M : Type _ → Type _} [Monad M] [HHLSyntax M] {α : Type _}
  (P : HHL.elemType M α → H.type M α) : H.type M α := fun S =>
  --¬ HHLSyntax.Forall (fun x => ¬ P x)
  ¬ H.Forall (fun x S => ¬ P x S) S
