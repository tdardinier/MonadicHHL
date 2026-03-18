import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal

instance (σ : Type) (m : Type → Type) [Monad m] [HHL m] : HHL (ReaderT σ m) where
  -- elemType α := elemType m (α × σ)
  elemType α := elemType m α × σ
  relWith {α β : Type} (C : α → ReaderT σ m β)
    (p : elemType m α × σ) (p' : elemType m β × σ) :=
    relWith (fun v => C v p.2) p.1 p'.1 ∧ p.2 = p'.2
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i x0 HHL_M x2 HHL_m
    have h := HHL_m.bind_rel (fun v₁ ↦ C₁ v₁ p₀.2) (fun v₂ ↦ C₂ v₂ p₂.2) p₀.1 p₂.1
    apply Iff.intro
    {
      intro h1
      have h := h.mp (by
        rw [HHL.relWith]
        aesop
      )
      rcases h with ⟨s1, hp1_rel, hp2_rel⟩
      apply Exists.intro (s1, p₀.2)
      aesop
    }
    {
      intro h1
      rcases h1 with ⟨p1, hp1_rel, hp2_rel⟩
      have h := h.mpr (by
        rw [HHL.relWith]
        aesop
      )
      have heq : (fun v₁ ↦ do let v₂ ← C₁ v₁ p₀.2; C₂ v₂ p₂.2)
        = (fun v ↦ (fun v₁ ↦ C₁ v₁ >>= C₂) v p₀.2) := by
        aesop
      aesop
    }
