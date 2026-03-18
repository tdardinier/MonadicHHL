import MonadicHHL.HHLMonads

section NonDeterministicTransformer

inductive NonDetT (m : Type u -> Type v) : (α : Type u) -> Type _ where
  | pure {α} (ret : α) : NonDetT m α
  | vis {α} {β} (x : m β) (f : β → NonDetT m α) : NonDetT m α
  | pickCont {α} (τ : Type u) (p : τ -> Prop) (f : τ → NonDetT m α) : NonDetT m α

variable {m : Type u -> Type v} {α β : Type u} [Monad m]

def NonDetT.bind (x : NonDetT m α) (f : α → NonDetT m β) : NonDetT m β :=
  match x with
  | pure ret => f ret
  | vis x f' => vis x fun y => bind (f' y) f
  | pickCont τ p f' => pickCont τ p fun t => bind (f' t) f

instance : Monad (NonDetT m) where
  pure := NonDetT.pure
  bind := NonDetT.bind

instance [LawfulMonad m] : LawfulMonad (NonDetT m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { introv; induction x
    <;> simp [Functor.map, NonDetT.bind]
    <;> solve_by_elim [funext] }
  { introv; simp [bind, NonDetT.bind] }
  introv; induction x
  <;> simp [bind, NonDetT.bind]
  <;> solve_by_elim [funext]

def NonDetT.pick (τ : Type u) : NonDetT m τ :=
  NonDetT.pickCont _ (fun _ => True) pure
def NonDetT.assume (as : Prop) : NonDetT m PUnit :=
  NonDetT.pickCont PUnit (fun _ => as) fun _ => pure .unit
def NonDetT.pickSuchThat (τ : Type u) (p : τ → Prop) : NonDetT m τ :=
  NonDetT.pickCont τ p pure

class MonadNonDet (m : Type u → Type v) where
  pick : (τ : Type u) →  m τ
  pickSuchThat : (τ : Type u) → (τ → Prop) → m τ
  assume : Prop → m PUnit.{u+1}

export MonadNonDet (pick assume pickSuchThat)

instance : MonadNonDet (NonDetT m) where
  pick   := .pick
  assume := .assume
  pickSuchThat := .pickSuchThat

end NonDeterministicTransformer

@[grind]
def choiceFunctions {A B : Type _} (f : A → Set B) : Set (A → B) :=
  { g | ∀ a : A, g a ∈ f a }

@[grind]
def NonDetT.toSet {α : Type u} {m : Type u → Type v} [Monad m]
    (x : NonDetT m α) : Set (m α) :=
  match x with
  | NonDetT.pure a => {Pure.pure a}
  | @NonDetT.vis _ _ β (x : m β) f =>
    have ff := (fun (b : β) => NonDetT.toSet (f b))
    have S : Set (β → m α) := choiceFunctions ff
    (fun f => x >>= f) '' S
  | NonDetT.pickCont _ p f => ⋃ t ∈ {t | p t}, NonDetT.toSet (f t)


instance (m : Type → Type) [Monad m] [HHL m] : HHL (NonDetT m) where
  elemType α := HHL.elemType m α
  relWith {α β : Type} (C : α → NonDetT m β)
    (p : HHL.elemType m α) (p' : HHL.elemType m β) :=
    ∃ g ∈ choiceFunctions (NonDetT.toSet ∘ C), HHL.relWith g p p'
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    sorry
    -- rename_i x0 HHL_M x2 HHL_m
    -- apply HHL_m.bind_rel (fun v₁ ↦ C₁ v₁.1 v₁.2) (fun v₂ ↦ C₂ v₂.1 v₂.2) p₀ p₂

----- I want HHL Set = HHL (NonDetT Id) -----

abbrev NonDet := NonDetT Id
-- should be the same as Set


lemma sanity_check_same_relWith {α β : Type _}
  (C : α → NonDet β) (p : α) (p' : β) :
  HHL.relWith C p p' ↔ HHL.relWith (fun a => NonDetT.toSet (C a)) p p'
  := by
    simp [HHL.relWith, choiceFunctions]

    induction (C p) with -- probably need to generalize a bunch of stuff?
    | pure ret =>
      simp [NonDetT.toSet, Pure.pure, NonDetT.toSet]
      apply Iff.intro
      {
        intro h
        rcases h with ⟨g, hg, hrel⟩
        specialize hg p
        sorry
      }
      {
        intro h
        rw [h]
        sorry
      }
      --HHL.relWith, choiceFunctions]
    | vis x f ih =>
      sorry
    | pickCont τ p f ih =>
      sorry
