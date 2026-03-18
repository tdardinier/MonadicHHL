import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal

open Lean.Order

inductive DivM (α : Type u) where
  | res (x : α)
  | div

def DivM.run {α : Type u} [Inhabited α] : DivM α -> α
  | DivM.res x => x
  | DivM.div => default

instance : Monad DivM where
  pure := DivM.res
  bind := fun x y => match x with
    | DivM.res x => y x
    | DivM.div => DivM.div

class CCPOBot (m : Type u -> Type v)  where
  compBot {α} : m α

class CCPOBotLawful (m : Type u -> Type v) [∀ α, CCPO (m α)] [CCPOBot m] where
  prop {α} : CCPOBot.compBot (m := m) (α := α) = bot

instance : LawfulMonad DivM := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { introv; cases x <;> rfl }
  { introv; rfl }
  introv; cases x <;> rfl

noncomputable instance : CCPO (DivM α)
:= inferInstanceAs (CCPO (FlatOrder .div))
instance : CCPOBot DivM where
  compBot := .div

instance : CCPOBotLawful DivM where
  prop := by simp [Lean.Order.bot, Lean.Order.CCPO.csup,Lean.Order.flat_csup, instCCPOBotDivM]

instance : Lean.Order.MonoBind DivM where
  bind_mono_left := by
    rintro _ _ (_|_) _ _ (_|_) <;> solve_by_elim
  bind_mono_right := by
    rintro _ _ (_|_) <;> solve_by_elim

/- partial loop from MonoBind and CCPO instances -/
@[specialize, inline]
def Loop.forIn.loop {m : Type u -> Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
  (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop f b
  partial_fixpoint

@[inline]
def Loop.forIn {β : Type u} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
  (_ : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  Loop.forIn.loop f init

@[instance high]
instance [md : Monad m] [ccpo : ∀ α, CCPO (m α)] [mono : MonoBind m] : ForIn m Lean.Loop Unit where
  forIn {β} _ := @Loop.forIn m β md ccpo mono

def Assume (P : Prop) [Decidable P] : DivM PUnit :=
  if P then DivM.res () else DivM.div

def nonterminatingDiv : DivM Int := do
  while true do
    return 1
  return 0

instance : HHL DivM where
  elemType := DivM
  relWith C p p' := match p with
    | DivM.div => p' = DivM.div
    | DivM.res x => p' = C x
  bind_rel C1 C2 p0 p2 := by
    simp [Bind.bind]
    cases p0
    · grind
    grind

instance : HHLWithVal DivM where
  getVal p := match p with
    | DivM.div => none
    | DivM.res x => some x
  mapElem f p := match p with
    | DivM.div => DivM.div
    | DivM.res x => DivM.res (f x)
  coerce p h := match p with
    | DivM.div => DivM.div
    | DivM.res x => by contradiction

instance : HHLWithValLawful DivM where
  inactive C σ σ' h := by
    simp [HHL.relWith, HHLWithVal.coerce]
    simp [HHLWithVal.getVal] at h
    cases σ
    {
      grind
    }
    {
      grind
    }
  active_congr p v h C D p' := by
    simp [HHL.relWith]
    simp [HHLWithVal.getVal] at h
    grind
