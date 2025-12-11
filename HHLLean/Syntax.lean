import HHLLean.Triples

structure charact_path (α : Type) where
  pc : State α → Bool
  subst : Var → Exp α

def id_charact_path {α : Type} : charact_path α :=
  { pc := fun _ => True,
    subst := fun y => var_exp y }

def characterizer (α : Type) : Type := List (charact_path α)


def update_characterizer {α : Type} (c : charact_path α): Stmt α → characterizer α
  | Stmt.skip => [c]
  | Stmt.assign x e => [ {
        pc := c.pc,
        subst := c.subst[x ↦ e]
  } ]
  | Stmt.seq C₁ C₂ =>
    (update_characterizer c C₁).flatMap (fun c => update_characterizer c C₂)
  | Stmt.branch C₁ C₂ =>
    (update_characterizer c C₁).append (update_characterizer c C₂)
  | Stmt.assume b =>
    [ {
        pc := fun σ => c.pc σ ∧ b (fun y => (c.subst y) σ),
        subst := c.subst
    } ]
  | _ => [] -- todo: more cases

def compute_characterizer {α : Type} (C : Stmt α) : characterizer α :=
  update_characterizer id_charact_path C

def if_fib : Stmt Int :=
  IfThenElse (fun σ ↦ σ "i" < σ "n")
    (Stmt.assign "tmp" (var_exp "b");
    Stmt.assign "b" (fun σ ↦ σ "a" + σ "b");
    Stmt.assign "a" (var_exp "tmp"); Stmt.assign "i" fun σ ↦ σ "i" + 1)
    Stmt.skip

#eval (compute_characterizer if_fib).length


/-! Basic syntactic objects -------------------------------------------------/

/- Basic stuff (adapt these to your actual project) ------------------------/

abbrev StateVar := String

/-- Syntactic program expressions with an explicit state variable. -/
inductive SynExp (α : Type) where
  | Lit   : α → SynExp α
  | Var   : StateVar → Var → SynExp α
  | Unop  : (α → α) → SynExp α → SynExp α
  | BinOp : SynExp α → (α → α → α) → SynExp α → SynExp α

/-- Parametric expressions (no explicit state variable yet). -/
inductive SynPExp (α : Type) where
  | Lit   : α → SynPExp α
  | Var   : Var → SynPExp α
  | Unop  : (α → α) → SynPExp α → SynPExp α
  | BinOp : SynPExp α → (α → α → α) → SynPExp α → SynPExp α

/-- Instantiate a parametric expression with a state variable name. -/
def PExp_to_Exp {α : Type} (σ : StateVar) : SynPExp α → SynExp α
  | SynPExp.Lit n          => SynExp.Lit n
  | SynPExp.Var x          => SynExp.Var σ x
  | SynPExp.Unop f e       => SynExp.Unop f (PExp_to_Exp σ e)
  | SynPExp.BinOp e₁ op e₂ =>
      SynExp.BinOp (PExp_to_Exp σ e₁) op (PExp_to_Exp σ e₂)


/- Assertions --------------------------------------------------------------/

inductive SynAssertion (α : Type) : Type where
  | Lit         : Bool → SynAssertion α
  | ForallState : StateVar → SynAssertion α → SynAssertion α
  | ExistsState : StateVar → SynAssertion α → SynAssertion α
  | Or          : SynAssertion α → SynAssertion α → SynAssertion α
  | And         : SynAssertion α → SynAssertion α → SynAssertion α
  | Cmp         : SynExp α → (α → α → Prop) → SynExp α → SynAssertion α

namespace SynAssertion

-- Literals
scoped notation "⊤ₛ" => SynAssertion.Lit true
scoped notation "⊥ₛ" => SynAssertion.Lit false

-- Boolean connectives
scoped infixr:35 " ∧ₛ " => SynAssertion.And
scoped infixr:30 " ∨ₛ " => SynAssertion.Or

-- Comparisons
scoped notation:50 e₁:51 " =ₛ " e₂:50 =>
  SynAssertion.Cmp e₁ (· = ·) e₂

scoped notation:50 e₁:51 " ≤ₛ " e₂:50 =>
  SynAssertion.Cmp e₁ (· ≤ ·) e₂

scoped notation:50 e₁:51 " <ₛ " e₂:50 =>
  SynAssertion.Cmp e₁ (· < ·) e₂


/- Surface syntax without quotes ------------------------------------------/


/-- Quantifiers with a *state-name* identifier: `∀⟨σ⟩, P` and `∃⟨σ⟩, P`. -/
scoped syntax "∀⟨" ident "⟩, " term : term
scoped syntax "∃⟨" ident "⟩, " term : term

macro_rules
  | `(∀⟨ $σ:ident ⟩, $P) =>
      let s : String := σ.getId.toString
      `(
        SynAssertion.ForallState $(Lean.quote s) $P
      )

  | `(∃⟨ $σ:ident ⟩, $P) =>
      let s : String := σ.getId.toString
      `(
        SynAssertion.ExistsState $(Lean.quote s) $P
      )

/-- `σ[v]` sugar for `SynExp.Var σ v`:

    * `σ` must be an identifier (used as a `StateVar` name),
    * `v` is **any term of type `Var`** (e.g. your parameter `t`).
-/
scoped syntax ident "[" term "]" : term

macro_rules
  | `($σ:ident[$v]) =>
      let sσ : String := σ.getId.toString
      `(
        SynExp.Var $(Lean.quote sσ) $v
      )

/-- `σ ⟦e⟧` sugar for `PExp_to_Exp σ e` with `σ` an identifier. -/
scoped syntax ident " ⟦" term "⟧" : term

macro_rules
  | `($σ:ident ⟦$e⟧) =>
      let sσ : String := σ.getId.toString
      `(
        PExp_to_Exp $(Lean.quote sσ) $e
      )


/- Example: syn_mono in nice syntax ----------------------------------------/

open SynAssertion
open scoped SynAssertion

instance : OfNat (SynExp Int) n where
  ofNat := SynExp.Lit n

def syn_negation {α : Type} : SynAssertion α → SynAssertion α
  | SynAssertion.Lit b         => SynAssertion.Lit (!b)
  | SynAssertion.ForallState σ P => SynAssertion.ExistsState σ (syn_negation P)
  | SynAssertion.ExistsState σ P => SynAssertion.ForallState σ (syn_negation P)
  | SynAssertion.Or P Q        => SynAssertion.And (syn_negation P) (syn_negation Q)
  | SynAssertion.And P Q       => SynAssertion.Or (syn_negation P) (syn_negation Q)
  | SynAssertion.Cmp e₁ op e₂  => SynAssertion.Cmp e₁ (fun a b => ¬ (op a b)) e₂

scoped prefix:70 "¬ₛ " => syn_negation

def syn_imp {α : Type} (P Q : SynAssertion α) : SynAssertion α :=
  ¬ₛ P ∨ₛ Q

scoped infixr:25 " →ₛ " => syn_imp

def syn_mono (t : Var) (e : SynPExp Int) : SynAssertion Int :=
  ∀⟨σ₁⟩, ∀⟨σ₂⟩, (σ₁[t] =ₛ 1 ∧ₛ σ₂[t] =ₛ 2) →ₛ σ₁ ⟦e⟧ ≤ₛ σ₂ ⟦e⟧

def apply_charact_to_SynAssertion {α : Type}
  (L : characterizer α) : SynAssertion α → SynAssertion α
  | SynAssertion.Lit b => SynAssertion.Lit b
  | SynAssertion.ForallState σ P =>
    let conjuncts := L.map (fun c =>
      ∀⟨σ⟩, c.pc σ → apply_charact_to_SynAssertion P)
  | _ => sorry


def square {α : Type} (b : State α → Prop) : hyperassertion α :=
  fun S => ∀ σ, S σ → b σ

def var_exp {α : Type} (x : Var) : Exp α :=
  fun σ => σ x
