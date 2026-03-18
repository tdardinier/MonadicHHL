import Lean
import Mathlib.Data.Set.Basic

open Lean

/-- Variable and value types (customize if you like). -/
abbrev Var := String
abbrev Val := Nat

/-- States map variables to values. -/
abbrev State := Var → Val

/-- Hyper-assertions: predicates on sets of states. -/
abbrev SPred := Set State → Prop

/-- Array-like notation: `σ["x"]` or `σ[x]`. -/
notation σ "[" v "]" => σ v

/--
State-quantifier binder:

  ∀⟨σ₁, σ₂, ...⟩, φ

has type `SPred` and expands to

  fun S : Set State =>
    ∀ (σ₁ : State), σ₁ ∈ S →
    ∀ (σ₂ : State), σ₂ ∈ S →
    ... → φ
-/
syntax "∀⟨" ident,+ "⟩, " term : term

macro_rules
  | `(∀⟨$xs:ident,*⟩, $body) => do
      -- `body` is already a `term`
      let mut acc : Term := body
      -- Build: ∀ (x : State), x ∈ S → acc, from right to left
      for x in xs.getElems.reverse do
        acc ← `(∀ ($x : State), $x ∈ S → $acc)
      -- Whole thing: Set State → Prop
      `(fun S : Set State => $acc)

/--
SPred quotation brackets: `⟪ φ ⟫`.

We give two behaviors:

* Special case for `⟪ ∃ v, ∀⟨σ₁, …, σₙ⟩, body ⟫`, which expands to
    `fun S => ∃ v, ∀ σ₁ ∈ S, …, ∀ σₙ ∈ S, body`

* Generic case `⟪ p ⟫` which is just a no-op and returns `p` as-is
  (useful when `p` already has type `SPred`).
-/
syntax "⟪" term "⟫" : term

-- More specific rule FIRST: existential + our custom state-quantifier.
macro_rules
  | `(⟪ ∃ $v, ∀⟨$xs:ident,*⟩, $body ⟫) => do
      let mut acc : Term := body
      -- Build: ∀ (x : State), x ∈ S → acc, for each σ in xs, right to left.
      for x in xs.getElems.reverse do
        acc ← `(∀ ($x : State), $x ∈ S → $acc)
      `(fun S : Set State => ∃ $v, $acc)

-- Fallback: brackets around an existing SPred do nothing.
macro_rules
  | `(⟪ $p ⟫) =>
      `($p)

/-! ### Your examples -/

example : SPred :=
  ⟪ ∃ v, ∀⟨σ⟩, σ["x"] = v ⟫

def one_example : SPred :=
  ∀⟨σ₁, σ₂⟩,
    (σ₁["t"] = 1 ∧ σ₂["t"] = 2) →
    σ₁["x"] ≤ σ₂["x"]

def low (x : Var) : SPred :=
  ∀⟨σ₁, σ₂⟩, σ₁[x] = σ₂[x]
