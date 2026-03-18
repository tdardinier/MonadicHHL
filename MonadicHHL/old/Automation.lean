import HHLLean.Triples

import Lean
import Lean.Meta
import Lean.Elab.Tactic

------------------------------
--- Example: Fibonacci
------------------------------

@[grind]
def interp {α : Type} (fuel : Nat) (C : Stmt α) (σ : State α) : List (State α) :=
if fuel = 0 then []
else
  match C with
  | Stmt.skip => [σ]
  | Stmt.assign x e => [σ[x ↦ e σ]]
  | Stmt.seq C₁ C₂ => (interp (fuel - 1) C₁ σ).flatMap (interp (fuel - 1) C₂)
  | Stmt.assume b => if b σ then [σ] else []
  | Stmt.branch C₁ C₂ => interp (fuel - 1) C₁ σ ++ interp (fuel - 1) C₂ σ
  | Stmt.loop (Stmt.assume b; C) =>
    if b σ then
      (interp (fuel - 1) C σ).flatMap (interp (fuel - 1) (Stmt.loop (Stmt.assume b; C)))
    else [σ]
  | Stmt.loop _ => [σ] -- todo: More iterations
  | Stmt.havoc _ => [] -- nondeterminism: todo

#check List.mem_singleton

lemma interp_correct {α : Type} (n : Nat) (C : Stmt α) (σ σ' : State α):
  List.Mem σ' (interp n C σ) → ⟨C, σ⟩ ⟹ σ' :=
  by
    induction n generalizing C σ σ' with
    | zero =>
      simp [interp.eq_def]
      intro h
      contradiction
    | succ n ih =>
      match C with
      | Stmt.skip =>
        simp [interp.eq_def]
        intro h
        rw [List.eq_of_mem_singleton h]
        apply BigStep.skip
      | Stmt.assign x e =>
        simp [interp.eq_def]
        intro h
        rw [List.eq_of_mem_singleton h]
        apply BigStep.assign
      | _ => sorry


def σ₀ : State Int :=
  fun _ => 0

-----------------------------------------------------
------- Verification
-----------------------------------------------------

theorem rule_while_forall_exists_intro {α : Type} {I Q : hyperassertion α} {b : BExp α} {C : Stmt α}
  (hinv : {* I *} (IfThenElse b C Stmt.skip) {* I *})
  (hpost : {* I *} (Stmt.assume (LNot b)) {* Q *}) :
    {* I *} (While b C) {* Q *} :=
  sorry

def WhileWithInvForEx {α} (b : BExp α) (_ : List (hyperassertion α)) (C : Stmt α) : Stmt α :=
  While b C

@[grind]
def conjoin {α : Type} : List (hyperassertion α) → hyperassertion α
  | []       => fun _ => True
  | [P]       => P
  | P :: tl  => fun S => P S ∧ conjoin tl S

theorem invWhile_intro {α : Type} {b I Q} {C : Stmt α}
  (hinv : {* conjoin I *} (IfThenElse b C Stmt.skip) {* conjoin I *})
  (hpost : {* conjoin I *} (Stmt.assume (LNot b)) {* Q *})
:
    {* conjoin I *} (WhileWithInvForEx b I C) {* Q *} := by
  apply rule_while_forall_exists_intro
  · exact hinv
  exact hpost

theorem invWhile_intro' {α : Type} {b I P Q} {C : Stmt α}
  (hinv : {* conjoin I *} (IfThenElse b C Stmt.skip) {* conjoin I *})
  (hpost : {* conjoin I *} (Stmt.assume (LNot b)) {* Q *})
  (hcons : ∀ S, P S → conjoin I S) :
    {* P *} (WhileWithInvForEx b I C) {* Q *} := by
  apply rule_cons
  {
    apply invWhile_intro
    · apply hinv
    exact hpost
  }
  · exact hcons
  simp

@[grind]
def h_mono (t : Var) (e : Exp Int) : hyperassertion Int :=
  fun S => ∀ σ₁ σ₂, S σ₁ ∧ S σ₂ ∧ σ₁ t = 1 ∧ σ₂ t = 2 → e σ₁ ≤ e σ₂

def square {α : Type} (b : State α → Prop) : hyperassertion α :=
  fun S => ∀ σ, S σ → b σ

def var_exp {α : Type} (x : Var) : Exp α :=
  fun σ => σ x

def fib : Stmt Int :=
    Stmt.assign "a" (fun _ => 0);
    Stmt.assign "b" (fun _ => 1);
    Stmt.assign "i" (fun _ => 0);
    WhileWithInvForEx
      (fun σ => σ "i" < σ "n")
      ([
        h_mono "t" (var_exp "a"),
        h_mono "t" (var_exp "b"),
        h_mono "t" (fun σ => σ "n - i"),
        square (fun σ => 0 ≤ σ "a" ∧ σ "a" ≤ σ "b")
      ])
      (Stmt.assign "tmp" (var_exp "b");
       Stmt.assign "b" (fun σ => σ "a" + σ "b");
       Stmt.assign "a" (var_exp "tmp");
       Stmt.assign "i" (fun σ => σ "i" + 1))

#eval List.map (fun σ => (σ "a", σ "b")) (interp 20 fib (σ₀["n" ↦ 10]))

theorem fib_correct :
  {* h_mono "t" (var_exp "n") *} (fib) {* h_mono "t" (var_exp "b") *} :=
  by
    sorry
/-
    simp [fib]
    apply rule_seq
    apply rule_seq
    apply rule_seq
    apply rule_seq
    apply rule_assume'
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
-/


---- Automation

open Lean

-- Fix: Account for the type argument (first Expr.app)
def matchPartialHoare : Expr → Option (Expr × Expr × Expr)
  | (Expr.app (Expr.app (Expr.app (Expr.app
       (Expr.const ``triple _) _) P) C) Q) =>
    Option.some (P, C, Q)
  | _ =>
    Option.none


open Lean.Meta
open Lean.Elab.Tactic

def applyConstant (name : Name) : TacticM Unit :=
  do
    let cst ← mkConstWithFreshMVarLevels name
    liftMetaTactic (fun goal ↦ MVarId.apply goal cst)



partial def vcg : TacticM Unit :=
  do
    -- logInfo m!"VCG started"
    let goals ← getUnsolvedGoals
    -- logInfo m!"Goals: {goals}"
    if goals.length != 0 then
      let target ← getMainTarget
      logInfo m!"target: {target}"
      match matchPartialHoare target with
      | Option.none           =>
        logInfo "None..."
        return
      | Option.some (P, C, Q) =>
        -- logInfo m!"Pattern matched!: {P} {C}"
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

elab "vcg" : tactic =>
  vcg

theorem fib_correct_auto :
  {* h_mono "t" (var_exp "n") *} (fib) {* h_mono "t" (var_exp "b") *} :=
  by
    rw [fib]
    vcg <;> try grind
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
