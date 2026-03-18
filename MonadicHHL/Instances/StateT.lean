import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal
-- import MonadicHHL.Instances.Id
import MonadicHHL.Instances.Set

open HHL
open HHLWithVal
open HHLWithValLawful

instance (σ : Type) (m : Type → Type) [Monad m] [HHL m] : HHL (StateT σ m) where
  elemType α := elemType m (α × σ)
  --elemType α := elemType m α × σ
  relWith {α β : Type} (C : α → StateT σ m β)
    (p : elemType m (α × σ)) (p' : elemType m (β × σ)) :=
    relWith (fun v ↦ C v.1 v.2) p p'
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i HHL_M HHL_m
    apply HHL_m.bind_rel (fun v₁ ↦ C₁ v₁.1 v₁.2) (fun v₂ ↦ C₂ v₂.1 v₂.2) p₀ p₂


variable (σ : Type)
-- #check (HHL.relWith (M := StateT σ Set))
#synth HHL (StateT σ Set)

lemma test_stateT_set1 (σ α : Type _) :
  elemType (StateT σ Set) α = (α × σ) := by
  rfl

lemma test_stateT_set2 {σ α : Type}
  (C : α → StateT σ Set α) (p p' : elemType (StateT σ Set) α)
  : relWith C p p' ↔ p' ∈ C p.1 p.2 := by
  rfl

instance {σ : Type _} (M : Type _ → Type _) [Monad M] [HHLWithVal M]
  : HHLWithVal (StateT σ M) where
  mapElem f p := mapElem (fun p => (f p.1, p.2)) p
  getVal σ := Option.map Prod.fst (getVal (M := M) σ)
  coerce {α β : Type _} (σ : HHL.elemType (M := M) (α × σ)) h :=
    coerce (M := M) σ (by aesop)

instance {σ : Type _} (M : Type _ → Type _) [Monad M] [HHLWithValLawful M]
  : HHLWithValLawful (StateT σ M) where
  inactive {α β : Type _}
    (C : α → StateT σ M β) (p : HHL.elemType (M := M) (α × σ)) (p' : HHL.elemType (M := M) (β × σ))
    (h : (getVal (M :=  StateT σ M) p).isNone) := by
    have hh := inactive (M := M) (fun p => C p.1 p.2) p p' (by
      simp [getVal] at h
      aesop)
    aesop
  active_congr {α β : Type _}
    (p : HHL.elemType (M := M) (α × σ)) (v : α)
    (h : getVal (M := StateT σ M) p = some v)
    (C D : α → StateT σ M β) (p' : HHL.elemType (M := M) (β × σ)) := by
    simp [getVal] at h
    rcases h with ⟨s, hv⟩
    simp [HHL.relWith]
    have hh := active_congr (M := M) p (v, s) (by aesop) (fun v ↦ C v.1 v.2) (fun v ↦ D v.1 v.2) p'
    aesop
