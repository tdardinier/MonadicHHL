import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal

open HHL

--- The unused type parameter is the logical part of the state
def LogicT (_ : Type) (m : Type _ → Type _) : Type _ → Type _
 := m

instance (L : Type) (m : Type _ → Type _) [M : Monad m] : Monad (LogicT L m) where
  pure := M.pure
  bind := M.bind

/-
def logicify {L : Type} {m : Type _ → Type _} [Monad m]
  (f : α → LogicT L m β) (x : α × L) : m β × L :=
    (f x.1, x.2)
-/

-- Like StateT basically?
-- How does this compose with the set base monad?
instance {m : Type _ → Type _} (L : Type) [Monad m] [HHL m] : HHL (LogicT L m) where
  elemType α := elemType m α × L
  --elemType α := elemType m (α × L)
  relWith --C p p' :=
   {α β : Type} (C : α → LogicT L m β)
   --(p : elemType m (α × L)) (p' : elemType m (β × L)) :=
   (p : elemType m α × L) (p' : elemType m β × L) :=
    @relWith m _ _ _ _ C p.1 p'.1
    ∧ p.2 = p'.2
    --relWith (logicify C) p p'
    -- relWith (fun v ↦ C v v) p p'
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i HHL_M HHL_m
    have h := HHL_m.bind_rel C₁ C₂ p₀.1 p₂.1
    aesop
