import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal

def exceptify {ε α β : Type _} {m : Type _ → Type _} [Monad m]
  (f : α → m (Except ε β)) : Except ε α → m (Except ε β)
  | Except.ok a => f a
  | Except.error e => pure (Except.error e)

open HHL

instance (ε : Type _) (m : Type _ → Type _) [Monad m] [HHL m] [LawfulMonad m]
  : HHL (ExceptT ε m) where
  elemType α := elemType m (Except ε α)
  relWith {α β : Type _}
    (f : α → m (Except ε β))
    (p : elemType m (Except ε α)) (p' : elemType m (Except ε β))
    := relWith (exceptify f) p p'
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i Monad_M Monad_m Lawful_m
    have h := bind_rel (exceptify C₁) (exceptify C₂) p₀ p₂

    have heq : (fun v₁ ↦ exceptify C₁ v₁ >>= exceptify C₂)
      = (exceptify fun v₁ ↦ @bind (ExceptT ε m) ExceptT.instMonad.toBind α₁ α₂ (C₁ v₁) C₂)
    := by
      apply funext
      intro p0
      simp [exceptify, Bind.bind, ExceptT.bind]
      cases p0
      {
        simp
        simp [exceptify]
      }
      {
        rename_i v0
        rw [Bind.bind]
        simp
        rw [ExceptT.mk]
        have heq : (exceptify C₂) =
        (fun v ↦ match v with | Except.ok a => C₂ a | Except.error e => pure (Except.error e))
        := by
          apply funext
          intro p
          simp [exceptify]
          aesop
        aesop
      }
    aesop
