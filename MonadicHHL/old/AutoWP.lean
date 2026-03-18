import Lean
import MonadicHHL.Characterizer

open Lean Parser Meta Elab Term Command Tactic

/-
-- Fix: Account for the type argument (first Expr.app)
def matchCharGen : Expr → Option Expr
  | (Expr.app (Expr.app (Expr.const ``CharGen _) _) C) => Option.some C
  | _ => Option.none

/-
structure CharGen {α β : Type _} (C : α → Id β) where
-/


open Lean.Meta
open Lean.Elab.Tactic

def applyConstant (name : Name) : TacticM Unit :=
  do
    let cst ← mkConstWithFreshMVarLevels name
    liftMetaTactic (fun goal ↦ MVarId.apply goal cst)


partial def get_char : TacticM Unit :=
  do
    -- logInfo m!"VCG started"
    let goals ← getUnsolvedGoals
    -- logInfo m!"Goals: {goals}"
    if goals.length != 0 then
      let target ← getMainTarget
      logInfo m!"target: {target}"
      match matchCharGen target with
      | Option.none           =>
        logInfo "None..."
        return
      | Option.some C =>
        logInfo m!"Pattern matched!: {C}"
        /-
        if Expr.isAppOfArity C ``Stmt.skip 1 then
          if Expr.isMVar P then
            applyConstant ``rule_skip
          else
            applyConstant ``rule_skip'
        else if Expr.isAppOfArity C ``Stmt.assign 3 then
          if Expr.isMVar P then
            applyConstant ``rule_assign
          else
            applyConstant ``rule_assign'
        else if Expr.isAppOfArity C ``Stmt.assume 2 then
          if Expr.isMVar P then
            applyConstant ``rule_assume
          else
            applyConstant ``rule_assume'
        else if Expr.isAppOfArity C ``Stmt.seq 3 then
          andThenOnSubgoals
            (applyConstant ``rule_seq') vcg
        /-else if Expr.isAppOfArity S ``Stmt.ifThenElse 3 then
          andThenOnSubgoals
            (applyConstant ``PartialHoare.if_intro) vcg
        -/
        else if Expr.isAppOfArity C ``Stmt.branch 3 then
          logInfo m!"Branch command: {C}"
          if Expr.isMVar Q then
            andThenOnSubgoals
              (applyConstant ``rule_branch) vcg
          else
            andThenOnSubgoals
              (applyConstant ``rule_branch') vcg
        else if Expr.isAppOfArity C ``WhileWithInvForEx 4 then
          logInfo m!"WhileWithInvForEx command: {C}"
          if Expr.isMVar P then
            logInfo m!"First branch"
            --applyConstant ``invWhile_intro
            --logInfo m!"Good"
            andThenOnSubgoals
              (applyConstant ``invWhile_intro) vcg
          else
            logInfo m!"Second branch"
            andThenOnSubgoals
              (applyConstant ``invWhile_intro') vcg
        else if Expr.isAppOfArity C ``IfThenElse 4 then
          logInfo m!"If then else"
          if Expr.isMVar Q then
            andThenOnSubgoals
              (applyConstant ``rule_branch) vcg
          else
            andThenOnSubgoals
              (applyConstant ``rule_branch') vcg
          logInfo "If: Unsure how to proceed"
          return
        else
          logInfo m!"No matching rule for command: {C}"
          failure
          -/

elab "get_char" : tactic =>
  get_char

def abs :Int → Id Int := fun x =>
  do
    if x > 0 then
      return x
    else
      return (-x)

example (x : Int) :
  have h : CharGen (if x > 0 then x else (-x)) := by
    get_char


-/


/-
def findSpec (prog : Expr) : TacticM (Array (Ident × Loom.SpecType)) := do
  let specs ← specAttr.find? prog
  let grts := specs.qsort (compare · · |>.isGT) |>.map
    fun ⟨specType, specName, _⟩ => (mkIdent specName, specType)
  return grts
-/

-- WPGen.{u, v} {m : Type u → Type v} [Monad m] {α l : Type u} [CompleteLattice l] [MAlgOrdered m l] (x : m α) : Type u
-- CharGen {α β : Type} (C : α → Id β) : Type


def Lean.MVarId.isCharGenGoal : MVarId → TacticM Bool
| mvarId => do
  let goalType <- mvarId.getType
  -- let_expr WPGen _m _mInst _α _l _lInst _mPropInst _ := goalType | return false
  let_expr CharGen _α _β _ := goalType | return false
  return true

def isCharGenGoal : TacticM Bool := do
  (<- getMainGoal).isCharGenGoal

def hideNonCharGenGoals : TacticM Unit := do
  let goals <- getGoals
  let goals' <- goals.filterM (·.isCharGenGoal)
  setGoals goals'

elab "is_not_chargen_goal" : tactic => do
  if ← isCharGenGoal then
    throwError "is a CharGen goal"
  else
    return

elab "hide_non_chargen_goals" : tactic => do
  hideNonCharGenGoals

/-- Get the value of a constant, or return the expression if it's not a constant -/
def getConstantValue (e : Expr) : MetaM Expr := do
  match e with
  | Expr.const name _ => do
    let info ← getConstInfo name
    match info.value? with
    | some val => return val
    | none => return e
  | _ => return e

/-- Fully reduce an expression, including delta reduction (unfolding definitions) -/
def reduceWithDelta (e : Expr) : MetaM Expr := do
  -- First try to get the constant's value directly
  let e_val ← getConstantValue e
  if e_val != e then
    -- If we got a value, check if it's a lambda and return it
    return e_val
  else
    -- Otherwise use whnf with default transparency (safer for bound variables)
    whnf e

/-- Detects if an expression is a lambda `fun v => Bind.bind (C1 v) C2` -/
def isBindPattern (e : Expr) : MetaM Bool := do
  let e ← reduceWithDelta e
  match e with
  | Expr.lam _ _ body _ =>
    -- Check the head of the body without further reduction
    -- to avoid bound variable issues
    match body.getAppFn with
    | Expr.const name _ =>
      if name == ``Bind.bind then
        return true
      else
        return false
    | _ => return false
  | _ => return false

/-- Detects if an expression is a lambda `fun v => ite (b v) (C1 v) (C2 v)` -/
def isItePattern (e : Expr) : MetaM Bool := do
  let e ← reduceWithDelta e
  match e with
  | Expr.lam _ _ body _ =>
    -- Check the head of the body without further reduction
    -- to avoid bound variable issues
    match body.getAppFn with
    | Expr.const name _ =>
      if name == ``ite then
        return true
      else
        return false
    | _ => return false
  | _ => return false


mutual
  /-- Helper to process all CharGen goals recursively -/
  partial def processCharGenGoals : TacticM Unit := do
    let allGoals ← getGoals
    let charGenGoals ← allGoals.filterM (·.isCharGenGoal)
    let nonCharGenGoals ← allGoals.filterM (fun g => do return !(← g.isCharGenGoal))
    if charGenGoals.length > 0 then
      -- Process the first CharGen goal
      setGoals ([charGenGoals[0]!] ++ nonCharGenGoals)
      charGenTactic
      -- After processing, check for new CharGen goals and continue
      processCharGenGoals

  /-- Main tactic that applies CharGen constructors recursively -/
  partial def charGenTactic : TacticM Unit := do
    let goalType ← getMainTarget
    let_expr CharGen _α _β C := goalType | return  -- Return early if not a CharGen goal

    -- Inspect the definition (with delta reduction) to detect patterns
    -- This doesn't modify the goal, just helps us decide which constructor to apply
    let C_norm ← reduceWithDelta C

    -- Try to detect bind pattern: fun v => C1 v >>= C2
    if ← isBindPattern C_norm then
      -- Use refine to let Lean infer C1, C2 from the goal
      evalTactic (← `(tactic| refine CharGen.bind ?_ ?_))
      -- Recursively handle all CharGen subgoals
      processCharGenGoals
      return

    -- Try to detect ite pattern: fun v => if b v then C1 v else C2 v
    if ← isItePattern C_norm then
      -- Use the more flexible CharGen.ite' which accepts the computation directly
      -- This avoids unification issues by letting Lean infer b, C1, C2
      evalTactic (← `(tactic| refine CharGen.ite' C ?_ ?_ ?_ ?_ ?_ ?_))
      -- Process all subgoals - use simp to help infer b, C1, C2 and prove equality
      let goals ← getGoals
      -- Process non-CharGen goals first with simp
      for goal in goals do
        if !(← goal.isCharGenGoal) then
          setGoals [goal]
          evalTactic (← `(tactic| simp))
      -- Then process CharGen goals recursively
      processCharGenGoals
      return

    -- Default case: apply CharGen.default
    evalTactic (← `(tactic| apply CharGen.default))
end

elab "char_gen" : tactic => charGenTactic



-- Test example: bind computation
def add_one_then_double (x : Int) : Id Int := do
  let y ← pure (x + 1)
  return (2 * y)

-- Test the tactic on a conditional
example (x : Int) : CharGen abs := by
  have h : CharGen (fun (x : Int) => if x > 0 then x else (-x)) := by
    char_gen

-- Test the tactic on a bind
example (x : Int) : CharGen add_one_then_double := by
  char_gen


elab "show_all_goals" : tactic => do
  setGoals (← getUnassignedExprMVars).toList
  synthesizeSyntheticMVarsNoPostponing

macro "try_resolve_spec_goals" : tactic => `(tactic| try is_not_chargen_goal; solve | rfl | solve_by_elim | simp)

/-- An ad-hoc solution to passing the termination check, by deriving
    conditions of the form `sizeOf x < sizeOf y` from equalities in the context.
    These equalities can be introduced by, for example, subgoals of `CharGen`. -/
/-
elab "chargen_generate_size_conditions" : tactic => do
  withMainContext do
  let goalType ← getMainTarget
  let_expr WPGen _m _mInst _α _l _lInst _mPropInst x := goalType | throwError "{goalType} is not a WPGen"
  let candidates ← x.getAppArgs'.filterM fun e => do
    unless e.isFVar do return false
    if Expr.isSort (← inferType e) then return false
    pure true
  for c in candidates do
    let cIdent ← Lean.mkIdent <$> c.fvarId!.getUserName
    let lctx ← getLCtx
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let_expr Eq _ a b := ty | continue
      unless a.isFVar || b.isFVar do continue
      if a == c || b == c then continue
      let larger := if c.occurs a then Option.some b else (if c.occurs b then some a else none)
      let some larger := larger | continue
      let .fvar larger := larger | continue
      let largerIdent ← Lean.mkIdent <$> larger.getUserName
      evalTactic (← `(tactic| have : sizeOf $cIdent:ident < sizeOf $largerIdent:ident := by
        subst $largerIdent ; simp))
-/

def generateCharStep : TacticM (Bool × Expr) := withMainContext do
  let goalType <- getMainTarget
  let_expr CharGen _α _β _ x := goalType | throwError "{goalType} is not a CharGen"
  if let some app ← matchMatcherApp? x then
    let name := app.matcherName
    if let some res ← Loom.Matcher.constructWPGen name then
      -- MetaM.run' <| /- realizeConst name (name ++ `WPGen) -/ (Loom.Matcher.defineWPGen name |>.run')
      /-
      error message: cannot add declaration test1.match_3.WPGen to environment as it is restricted to the prefix test1_correct
      -/
      withMainContext do
        let goal ← getMainGoal
        let tmp ← Loom.Matcher.partiallyInstantiateWPGen #[_α, _m, _mInst, _l] res app
        let goals ← goal.apply tmp
        replaceMainGoal goals
      return (true, x)
  let cs <- findSpec x
  for elem in cs do
    try
      match elem with
      | (spec, .wpgen) =>
        evalTactic $ <- `(tactic| apply $spec)
      | (spec, .triple) =>
        let info ← getConstInfo spec.getId
        let num_args := info.type.getNumHeadForalls
        let refine_part ←
          Array.foldlM
            (fun x li => `(term|$x $li))
            (←`(term| $spec))
            (Array.replicate num_args (←`(term|?_)))
        let refine_tac ← `(tactic|refine $refine_part)
        try
          evalTactic $ <- `(tactic|
          eapply $(mkIdent ``WPGen.spec_triple);
          apply $spec)
          return (true, x)
        catch _ =>
          evalTactic $ <- `(tactic|
          eapply $(mkIdent ``WPGen.spec_triple);
          $refine_tac)
          return (true, x)
      return (true, x)
    catch _ => continue
  let some ⟨rsx, _⟩ := x.getAppFn.const? | return (false, x)
  let rsxCorrect := (rsx.toString ++ "_correct").toName
  let some mainName ← getDeclName? | throwError s!"no lemma name found for goal:{goalType}"
  if mainName ≠ rsxCorrect then
    return (false, x)
  let mainNameIdent := mkIdent mainName
  try
    evalTactic $ <- `(tactic|
        wpgen_generate_size_conditions;
        eapply $(mkIdent ``WPGen.spec_triple);
        apply $mainNameIdent)
    return (true, x)
  catch _ =>
    return (false, x)


elab "wpgen_app" : tactic => do
  let (found, x) ← generateWPStep
  unless found do throwError "no spec found for {x}"

macro "wpgen_step" : tactic => `(tactic| first
  | (wpgen_app <;> intros <;> try_resolve_spec_goals)
  --| (intros; split <;> intros)
  )
macro "wpgen_intro" : tactic => `(tactic| (apply WPGen.intro; rotate_right))
macro "wpgen" : tactic => `(tactic| (
  wpgen_intro
  repeat' wpgen_step
  ))

def abs : Int → Id Int := fun x =>
  do
    if x > 0 then
      return x
    else
      return (-x)


#eval abs (-5)  -- should be 5

def charact_for_abs : characterizer Int Int :=
  Characterizer.ite
    (fun x => x > 0)
    (Characterizer.generic  -- then branch
      (fun x => x))
    (Characterizer.generic  -- else branch
      (fun x => -x))

#reduce charact_for_abs


















































open Lean Meta

/-- What we want to count. -/
structure Stats where
  branches : Nat := 0   -- if / ite / dite
  binds    : Nat := 0   -- monadic bind (Bind.bind)
  returns  : Nat := 0   -- monadic pure (Pure.pure)
deriving Repr

/-
Traverse an expression and count:

* `ite` / `dite`   → branches
* `Bind.bind`      → binds
* `Pure.pure`      → returns

We deliberately do **not** call `whnf` here so that we see
the actual heads that the elaborator produced.
-/

namespace Playground

inductive Expr where
  | bvar    : Nat → Expr                              -- bound variables
  | fvar    : FVarId → Expr                           -- free variables
  | mvar    : MVarId → Expr                           -- meta variables
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- constants
  | app     : Expr → Expr → Expr                      -- application
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda abstraction
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- (dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                          -- literals
  | mdata   : MData → Expr → Expr                     -- metadata
  | proj    : Name → Nat → Expr → Expr                -- projection

end Playground

abbrev dep_list : Type _ := List (Sum String Name)

def sstr (s : String) : dep_list :=
  [Sum.inl s]

/-- A small function `Int → Id Int` using `do`-notation and `if`. -/
def abs_alt (x : Int) : Id Int := do
  if x < 0 then
    let y := -x
    return y
  else
    return x


partial def compute_characterizer (e : Expr) : characterizer Int Int :=
  match_expr e with
  | ite _ c _ t f => Characterizer.ite (fun x => x < 0) (compute_characterizer t) (compute_characterizer f)
  --| Pure.pure _ _ => return sstr "pure 2"
  --| Pure.pure _ _ _ => return sstr "pure 3"
  | Pure.pure a b c d => Characterizer.pure 5
  | _ =>
    match e with
    | Expr.letE _ ty e₁ e₂ _ => Characterizer.bind (compute_characterizer e₁) (compute_characterizer e₂)
    | _ => Characterizer.generic (fun x => pure x )

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → β → Prop) :
  is_WP C
    (H.forall (fun σ1 => H.exists (fun σ2 => H.pure (Q σ1 σ2))))
    (WP.forall charac (fun σ1 => WP.exists charac (fun σ2 => H.pure (Q σ1 σ2))))
  := by grind


partial def compute_WP_from_charact
-- {α β : Type _}
  (charac : characterizer Int Int)
  (post : Expr) -- hyperassertion β
  : hyperassertion Int :=
  match_expr post with
  | H.forall _ _ body _ => WP.forall charac (fun _ => compute_WP_from_charact charac body)
  | _ => H.pure true


def compCharact (declName : Name) : MetaM (characterizer Int Int) := do
  let env ← getEnv
  let some ci := env.find? declName
    | throwError "unknown constant {declName}"
  let some val := ci.value?
    | throwError "constant {declName} has no value (maybe theorem/opaque?)"

  lambdaTelescope val fun _params body => do
    return compute_characterizer body

#reduce (do
  let s ← compCharact ``abs_alt
  -- let s ← compCharact ``just_ret
  pure s)




#print abs_alt

partial def convertExpr (e : Expr) : MetaM dep_list :=
do
  logInfo m!"Converting expression: {e}"
  match_expr e with
  | ite _ c _ t f =>
    return sstr "ite"
      --++ convertExpr c
      ++ (← convertExpr t) ++ (← convertExpr f)
  --| Pure.pure _ _ => return sstr "pure 2"
  --| Pure.pure _ _ _ => return sstr "pure 3"
  | Pure.pure _ _ _ _ => return sstr "pure 4"
  | Expr.letE _ ty e₁ e₂ _ =>
      return sstr "letE"
      -- ++ convertExpr ty
      ++ (← convertExpr e₁) ++ (← convertExpr e₂)
  | _ =>
 -- return sstr "other"
    match e with
    | Expr.letE _ ty e₁ e₂ _ =>
        return sstr "bind (letE)"
        -- ++ convertExpr ty
        ++ (← convertExpr e₁) ++ (← convertExpr e₂)
    | _ => return sstr "other"
    /-
    | Expr.bvar _ => return sstr "bvar"
    | Expr.fvar _ => return sstr "fvar"
    | Expr.mvar _ => return sstr "mvar"
    | Expr.sort _ => return sstr "sort"
    | Expr.const n _ => return [Sum.inl "const", Sum.inr n]
    | Expr.app fn arg => return sstr "app" ++ (← convertExpr fn) -- ++ (← convertExpr arg)
    | Expr.lam n ty body _ => return sstr "lam" ++ [Sum.inr n] ++ (← convertExpr ty) ++ (← convertExpr body)
    | Expr.lit _ => return sstr "lit"
    | _ => return sstr "other"
    -/

def analyseDecl (declName : Name) : MetaM dep_list := do
  let env ← getEnv
  let some ci := env.find? declName
    | throwError "unknown constant {declName}"
  let some val := ci.value?
    | throwError "constant {declName} has no value (maybe theorem/opaque?)"

  lambdaTelescope val fun _params body => do
    convertExpr body

def just_ret (x: Int) : Id Int :=
  return x

#eval (do
  let s ← analyseDecl ``abs_alt
  -- let s ← analyseDecl ``just_ret
  pure s
: MetaM dep_list)



def analyseExpr (e : Expr) : MetaM Stats := do
  logInfo m!"Analysing expression: {e}"
  e.foldlM
    (fun acc sub => do
      let some name := sub.getAppFn.constName?
        | return acc

      let acc :=
        if name == ``ite || name == ``dite then
          { acc with branches := acc.branches + 1 }
        else if name == ``Bind.bind then
          { acc with binds := acc.binds + 1 }
        else if name == ``Pure.pure then
          { acc with returns := acc.returns + 1 }
        else
          acc

      return acc)
    {}



def consumesExpr (e : Expr) : MetaM Unit :=
  IO.println s!"got: {e}"

/- Run the analysis on `test`. -/

/-
#eval show IO Unit from do
  let e : Expr := mkConst ``test   -- Expr for the constant `test`
  (consumesExpr e).run' {}
-/
