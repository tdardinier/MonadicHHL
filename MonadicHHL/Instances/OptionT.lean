import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal
import MonadicHHL.Instances.Id

def optionify {α β : Type _} {m : Type _ → Type _} [Monad m]
  (f : α → m (Option β)) : Option α → m (Option β)
  | some a => f a
  | none   => pure n

open HHL
------------ OptionT ---------------

instance (m : Type _ → Type _) [Monad m] [HHL m] [LawfulMonad m] : HHL (OptionT m) where
  elemType α := elemType m (Option α)
  relWith {α β : Type}
    (f : α → m (Option β))
    (p : elemType m (Option α)) (p' : elemType m (Option β))
    := relWith (optionify f) p p'
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i HHL_M HHL_m Lawful_m
    have h := HHL_m.bind_rel (optionify C₁) (optionify C₂) p₀ p₂

    have heq : (fun v₁ ↦ optionify C₁ v₁ >>= optionify C₂)
      = (optionify fun v₁ ↦ @bind (OptionT m) OptionT.instMonad.toBind α₁ α₂ (C₁ v₁) C₂)
    := by
      apply funext
      simp [optionify, Bind.bind, OptionT.bind]
      intro p0
      cases p0
      {
        simp
        simp [optionify]
      }
      {
        rename_i v0
        rw [Bind.bind]
        simp
        rw [OptionT.mk]
        have heq : (optionify C₂) = (fun v ↦ match v with | some a => C₂ a | none => pure none)
        := by
          apply funext
          intro p
          simp [optionify]
          aesop
        aesop
      }
    aesop

-- m : option unit?
def assertT (m : Type → Type) [Monad m] : Bool → OptionT m Unit
  | true  => @pure m _ _ (Option.some ())
  | false => @pure m _ _ (Option.none)

def liftToOptionT {m : Type → Type} [Monad m] {α β : Type}
  (C : α → m β) : α → OptionT m β := fun x =>
    let y : m β := C x
    OptionT.lift y

#check OptionT.lift

def liftHyperassertionToOptionT_aux {m : Type → Type} [Monad m] [HHL m] [LawfulMonad m]
  {α : Type} (P : Set (elemType m α) → Prop) (S : Set (elemType m (Option α))) : Prop :=
  sorry
  -- Annoying part: Should I specify that P has no error state at the start?
  -- Or the property about error states is preserved?


def liftHyperassertionToOptionT {m : Type → Type} [Monad m] [HHL m] [LawfulMonad m]
  {α : Type} (P : @HHL.hyperassertion m _ _ α) : @HHL.hyperassertion (OptionT m) _ _ α :=
  --fun (S : Set (Option α)) => P (Option.some '' S)
  -- fun (S : Set (Option α)) => P (semify (fun a => OptionT.lift (Pure.pure a)) S)
  liftHyperassertionToOptionT_aux P

/-
lemma lift_triple_OptionT {m : Type → Type} [Monad m] [HHL m]
  {α β : Type}
  {P : @HHL.hyperassertion m _ _ α}
  {C : α → m β}
  {Q : @HHL.hyperassertion m _ _ β}
  (h : HHL.triple P C Q) :
  HHL.triple P (liftToOptionT C) Q :=
  by
    simp [HHL.triple, HHL.semify, liftToOptionT, OptionT.lift, optionify]
    aesop
    -/


/-
@[always_inline, inline] protected def lift (x : m α) : OptionT m α := OptionT.mk do
  return some (← x)
-/




-- #check (HHL.relWith (M := StateT σ Set))
-- set_option diagnostics true
#synth HHL (OptionT Id)

lemma test_HHL_Option1 (α : Type _) :
  elemType (OptionT Id) α = Option α := by
  rfl

lemma test_HHL_Option2 {α : Type}
  (C : α → (OptionT Id) α) (p p' : elemType (OptionT Id) α)
  : relWith C p p' ↔ (match p with
    | some v => p' = C v
    | none => p' = none
  )
  := by
    simp [HHL.relWith, optionify, pure]
    aesop

/-
lemma rel_with_if_specialized_to_option {α β : Type}
  {C1 C2 : α → OptionT Id β}
  {p : elemType (OptionT Id) α}
  {p' : elemType (OptionT Id) β}
  {b : α → Bool}
  :
relWith (fun v ↦ if b v then C1 v else C2 v) p p'
↔ (relWith C1 p p' ∨ relWith C2 p p')
:= by
  simp [HHL.relWith, optionify, pure]
  cases p
  · simp
  simp
  rename_i v


  cases v
  {
    simp

  }
  -/

open HHLWithVal

instance (M : Type _ → Type _) [Monad M] [LawfulMonad M] [HHLWithVal M]
  : HHLWithVal (OptionT M) where

  mapElem f := mapElem (Option.map f)
  getVal σ := Option.join (getVal σ)
  coerce σ h :=
    match hv : getVal (M := M) σ with
    | none => coerce σ (by simp [hv])
    | some none => mapElem (fun _ => none) σ
    | some (some v) => by aesop

open HHLWithValLawful in
instance (M : Type _ → Type _) [Monad M] [LawfulMonad M] [HHLWithValLawful M]
  : HHLWithValLawful (OptionT M) where
  inactive {α β : Type _}
    (C : α → OptionT M β) (σ : HHL.elemType (OptionT M) α) (σ' : HHL.elemType (OptionT M) β)
    (h : (getVal σ).isNone) := by
    have hor : getVal (M := M) σ = none ∨ getVal (M := M) σ = some none := by
      simp [getVal, Option.join] at h
      cases hv : getVal (M := M) σ
      {
        left
        rfl
      }
      · aesop
    simp [HHL.relWith]
    have hh := inactive (optionify C) σ σ'
    cases hor
    {
      rename_i h_none
      have hh := inactive (optionify C) σ σ' (by
        simp [h_none]
      )
      sorry
    }
    {
      rename_i h_some_none
      specialize hh
      sorry
    }

  active_congr σ v h C D σ' := by
    simp [HHL.relWith]
    have heq : getVal (M := M) σ = some (some v) := by
      simp [getVal] at h
      simp [Option.join, Option.bind] at h
      aesop
    have hh := active_congr σ v heq (optionify C) (optionify D) σ'
    aesop
