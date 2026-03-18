import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal

-- import Mathlib.Logic.Function.Basic
-- import Mathlib.Order.CompleteBooleanAlgebra
-- import Mathlib.Order.Lattice
-- import Mathlib.Order.Basic

-------------------------------
------- Preliminaries ---------
-------------------------------

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | S, f => {b | ∃a, a ∈ S ∧ b ∈ f a}

instance : Monad Set where
  pure := Set.pure
  bind := Set.bind

instance : LawfulMonad Set where
  pure_bind  :=
    by
      intro α β a f
      simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
  bind_pure_comp  :=
    by
      intro α ma
      simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
      simp [Functor.map, Set.image]
      aesop
  bind_assoc :=
    by
      intro α β γ f g ma
      simp [Bind.bind, Set.bind]
      apply Set.ext
      aesop
  seqLeft_eq := sorry
  seqRight_eq := sorry
  pure_seq := sorry
  bind_map := sorry

def nonterminating : Set Int := do
  while true do
    return 1
  return 0

instance : HHL Set where
  elemType := Id
  relWith C p p' := p' ∈ C p
  bind_rel := by
    aesop
