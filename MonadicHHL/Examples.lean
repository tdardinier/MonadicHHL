import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal

import MonadicHHL.Instances.Set
import MonadicHHL.Instances.StateT
import MonadicHHL.Instances.LogicT
import MonadicHHL.Instances.OptionT

open HHL

abbrev LHHL_Monad (L σ α : Type) : Type :=
  LogicT L (StateT σ Set) α

lemma rel_with_LHHL_Monad (L σ α β : Type)
  (C : α → LHHL_Monad L σ β)
  (p : (α × σ) × L) (p' : (β × σ) × L) :
  HHL.relWith C p p' ↔ (p.2 = p'.2 ∧ p'.1 ∈ C p.1.1 p.1.2)
  := by
  simp [HHL.relWith]
  aesop

lemma semify_HHL (L σ α₁ α₂ : Type)
  (C : α₁ → LHHL_Monad L σ α₂)
  (S : Set ((α₁ × σ) × L)) :
  HHL.semify C S = { p' | ∃ p ∈ S, p.2 = p'.2 ∧ p'.1 ∈ C p.1.1 p.1.2 }
  := by
  simp [HHL.semify]
  --have h := rel_with_LHHL_Monad L σ α₁ α₂ C
  apply Set.ext
  intro p2
  simp [HHL.relWith]
  apply Iff.intro
  {
    intro h
    rcases h with ⟨p, hpS, hpRel⟩
    apply Exists.intro p.1.1
    apply Exists.intro p.1.2
    have heq : ((p.1.1, p.1.2), p2.2) = p := by aesop
    aesop
  }
  {
    intro h
    aesop
  }


abbrev weird_monad (L σ α : Type) : Type :=
  StateT σ (LogicT L Set) α

lemma same_monads :
  weird_monad = LHHL_Monad :=
  rfl

lemma same_elemType (L σ : Type) :
  HHL.elemType (weird_monad L σ) = HHL.elemType (LHHL_Monad L σ) :=
  rfl

lemma same_rel_with (L σ : Type) :
  @HHL.relWith (weird_monad L σ) = @HHL.relWith (LHHL_Monad L σ) :=
  rfl



abbrev HHL_Monad (σ α : Type) : Type :=
  StateT σ Set α

lemma semify_for_HHL {σ α₁ α₂ : Type}
  (C : α₁ → HHL_Monad σ α₂) (S : Set (α₁ × σ)) :
  HHL.semify C S = { p' | ∃ p ∈ S, p' ∈ C p.1 p.2 }
:= rfl

abbrev Hypra_Monad (σ α : Type) : Type :=
  OptionT (StateT σ Set) α

variable {σ : Type}
#synth HHL (StateT σ Set)
#synth LawfulMonad (OptionT (StateT σ Set))
#synth HHL (OptionT (StateT σ Set))

lemma relWith_Hypra {σ α₁ α₂ : Type}
  (C : α₁ → Hypra_Monad σ α₂)
  (p : Option α₁ × σ)
  (p' : Option α₂ × σ) :
  HHL.relWith C p p' ↔
    (p.1 = none ∧ p'.1 = none ∧ p.2 = p'.2) ∨
    (∃ v, p.1 = some v ∧ p' ∈ C v p.2)
:= by
  simp [HHL.relWith, optionify, pure]
  cases p.1
  {
    simp
    simp [StateT.pure, pure, Set.pure]
    grind
  }
  simp

lemma semify_for_Hypra {σ α₁ α₂ : Type}
  (C : α₁ → Hypra_Monad σ α₂) (S : Set (Option α₁ × σ)) :
  HHL.semify C S =
  { p' | ∃ p ∈ S, (p.1 = none ∧ p'.1 = none ∧ p.2 = p'.2) ∨ (∃ v, p.1 = some v ∧ p' ∈ C v p.2) }
:= by
  simp [HHL.semify]
  have h := relWith_Hypra C
  apply Set.ext
  intro x
  simp [HHL.relWith, optionify, pure]
  apply Iff.intro
  {
    intro h
    rcases h with ⟨p, hpS, hpRel⟩
    sorry
  }
  {
    sorry
  }


syntax (name := checkUnfolding) "#check " term " unfolding " ident* : command

open Lean Elab Command Meta
@[command_elab checkUnfolding]
def elacCheckUnfolding : CommandElab
  | `(#check%$tk $term unfolding $ids:ident*) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_check do
    if let `($id:ident) := term then
      try
        for c in (← realizeGlobalConstWithInfos term) do
          addCompletionInfo <| .id term id.getId (danglingDot := false) {} none
          let mut «type» ← Meta.inferType (← mkConstWithLevelParams c)
          for id in ids do
            «type» := (← Meta.unfold «type» id.getId).expr
          logInfoAt tk <| .signature c
          logInfoAt tk m!"{«type»}"
          return
      catch _ => pure ()
  | _ => throwUnsupportedSyntax


abbrev MonadT : Type _ := (Type _ → Type _) → Type _ → Type _


def asym_triple {α : Type}
  (P : Set α → Prop) (C : α → Option α) (Q : Set (Option α) → Prop) : Prop
  :=
  (∀ S, P S → Q (C '' S))

def the {α : Type} [Inhabited α] (x : Option α) : α :=
  Option.getD x (Inhabited.default)

/-
lemma hyperassertion_option {α : Type} :
  @HHL.elemType (OptionT Id) _ _ α = Option α := b
  rfl

  Maybe nice syntactic rule?
-/
lemma asym_triple_equiv {α : Type} [Inhabited α]
  (P : Set α → Prop) (C : α → OptionT Id α) (Q : Set (OptionT Id α) → Prop) :
  asym_triple P C Q
  ↔ @HHL.triple (OptionT Id) _ _ _ _ (fun S => P (the '' S) ∧ (∀ σ ∈ S, σ ≠ none)) C Q :=
  by
    simp [asym_triple, HHL.triple, HHL.elemType]
    simp [HHL.semify]
    apply Iff.intro
    {
      intro h
      intro S
      intro hP
      have hQ := h (the '' S)
      sorry
    }
    {
      intro h
      intro S
      intro hP
      sorry
    }
