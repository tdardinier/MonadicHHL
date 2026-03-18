import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
-- import Mathlib.Order.Lattice
-- import Mathlib.Order.Basic

lemma prove_prop_by_eq {α : Type _} {x y : α}
  (P : α → Prop)
  (h : x = y) :
  P x ↔ P y := by
    rw [h]


--------------------------------
-------- HHL typeclass ---------
--------------------------------

class HHL (M : Type _ → Type _) [Monad M] where
  elemType (α : Type _) : Type _
  relWith : {α β : Type _} → (α → M β) → elemType α → elemType β → Prop
  bind_rel
    {α₀ α₁ α₂ : Type _}
    (C₁ : α₀ → M α₁) (C₂ : α₁ → M α₂)
    (p₀ : elemType α₀) (p₂ : elemType α₂) :
      relWith (fun v₁ ↦ bind (C₁ v₁) C₂) p₀ p₂
      ↔ ∃ p₁, relWith C₁ p₀ p₁ ∧ relWith C₂ p₁ p₂

section

namespace HHL

variable {M : Type _ → Type _} [Monad M] [HHL M]  -- pretend we live in a world with a MyClass α


def semify {α₁ α₂ : Type}
  (C : α₁ → M α₂) : Set (elemType M α₁) → Set (elemType M α₂) :=
  fun S => { p' | ∃ p ∈ S, relWith C p p'}

lemma semify_bind {α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M α₂)
  (C₂ : α₂ → M α₃)
  (S : Set (elemType M α₁))
  :
 semify (fun v₁ ↦ bind (C₁ v₁) C₂) S = semify C₂ (semify C₁ S)
 := by
  simp [semify]
  apply Set.ext
  intro p'
  simp
  have h := bind_rel C₁ C₂
  aesop

/-
lemma semify_if_sync {α β : Type _}
  (C1 C2 : α → M β) (b : Bool)
  (S : Set (elemType M α)) :
  (b → semify (fun v ↦ if b then C1 v else C2 v) S = semify C1 S)
  ∧
  (¬b → semify (fun v ↦ if b then C1 v else C2 v) S = semify C2 S)
 := by
  simp [semify]
  aesop
-/




/-
lemma rel_with_if_specialized {α : Type}
  (C1 C2 : Bool → M α)
  (p : elemType M Bool)
  (p' : elemType M α)
  :
relWith (fun b ↦ if b = true then C1 b else C2 b) p p'
↔ (relWith C1 p p' ∨ relWith C2 p p')
:=
sorry



lemma semify_if {α : Type}
  (C1 : Bool → M α) (C2 : Bool → M α) (S : Set (elemType M Bool)) :
  semify (fun b ↦ if b then C1 b else C2 b) S = semify C1 S ∪ semify C2 S
 := by
  simp [semify]
  apply Set.ext
  intro p'
  simp
  have h := rel_with_if_specialized C1 C2
  aesop
-/

def hyperassertion (α : Type _) : Type _ :=
  Set (elemType M α) → Prop

def W (α₁ α₂ : Type _) : Type _ :=
  @hyperassertion M _ _ α₂ → @hyperassertion M _ _ α₁

def WP {α₁ α₂ : Type}
  (C : α₁ → M α₂) : @W M _ _ α₁ α₂ :=
  fun Q S => Q (semify C S)

lemma WP_bind {α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M α₂)
  (C₂ : α₂ → M α₃) :
  WP (C₁ >=> C₂) = (WP C₁) ∘ (WP C₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    apply propext
    simp [WP]
    apply prove_prop_by_eq
    have h := semify_bind C₁ C₂ S
    aesop

/-
lemma WP_if_sync {α β : Type _}
  (C1 C2 : α → M β) (b : Bool) :
  WP (fun v ↦ if b then C1 v else C2 v) =
    if b then WP C1 else WP C2
 := by
  have h := semify_if_sync C1 C2 b
  aesop
-/

lemma WP_cons {α β : Type _}
  (C : α → M β)
  (Q₁ Q₂ : @hyperassertion M _ _ β) :
  (∀ S, Q₁ S → Q₂ S) →
  (∀ S, WP C Q₁ S → WP C Q₂ S) := by
    intros h
    simp [WP, semify]
    aesop

abbrev H.and {α : Type _} (P Q : hyperassertion (M := M) α) : hyperassertion (M := M) α
:= fun S => P S ∧ Q S

abbrev H.or {α : Type _} (P Q : hyperassertion (M := M) α) : hyperassertion (M := M) α
:= fun S => P S ∨ Q S

abbrev H.forall {α β : Type _} (P : α → hyperassertion (M := M) β) : hyperassertion (M := M) β
:= fun S => ∀ x, P x S

abbrev H.exists {α β : Type _} (P : α → hyperassertion (M := M) β) : hyperassertion (M := M) β
:= fun S => ∃ x, P x S

abbrev H.true {α : Type _} : hyperassertion (M := M) α
:= fun _ => True

abbrev H.false {α : Type _} : hyperassertion (M := M) α
:= fun _ => False

abbrev H.join {α : Type _} (P Q : hyperassertion (M := M) α) : hyperassertion (M := M) α
:= fun S => ∃ S1 S2, S = S1 ∪ S2 ∧ P S1 ∧ Q S2


lemma WP_and {α β : Type _}
  (C : α → M β)
  (Q₁ Q₂ : @hyperassertion M _ _ β) :
  WP C (H.and Q₁ Q₂) = H.and (WP C Q₁) (WP C Q₂) := by
  apply funext
  aesop

lemma WP_or {α β : Type _}
  (C : α → M β)
  (Q₁ Q₂ : @hyperassertion M _ _ β) :
  WP C (H.or Q₁ Q₂) = H.or (WP C Q₁) (WP C Q₂) := by
  apply funext
  aesop

lemma WP_forall {α β γ : Type _}
  (C : α → M β)
  (Q : γ → @hyperassertion M _ _ β) :
  WP C (H.forall Q) = H.forall (fun x => WP C (Q x)) := by
  apply funext
  aesop

lemma WP_exists {α β γ : Type _}
  (C : α → M β)
  (Q : γ → @hyperassertion M _ _ β) :
  WP C (H.exists Q) = H.exists (fun x => WP C (Q x)) := by
  apply funext
  aesop

lemma WP_false {α β : Type _}
  (C : α → M β) :
  WP C H.false = H.false := by
  apply funext
  aesop



-----------------------------------------
------ Triples
-----------------------------------------


def triple {α₁ α₂ : Type _}
  (P : @hyperassertion M _ _ α₁)
  (C : α₁ → M α₂)
  (Q : @hyperassertion M _ _ α₂) : Prop :=
  ∀ S, P S → Q (semify C S)

lemma triple_equiv {α β : Type _}
  (P : hyperassertion α)
  (C : α → M β)
  (Q : hyperassertion β) :
  triple P C Q ↔ (∀ S, P S → WP C Q S) :=
  by
    simp [triple, WP]

lemma rule_seq {α₁ α₂ α₃ : Type _}
  {C1 : α₁ → M α₂}
  {C2 : α₂ → M α₃}
  {P : @hyperassertion M _ _ α₁}
  {R : @hyperassertion M _ _ α₂}
  {Q : @hyperassertion M _ _ α₃}
  (h1 : triple P C1 R)
  (h2 : triple R C2 Q) :
  triple P (C1 >=> C2) Q
  := by
    simp [triple_equiv] at *
    have h := WP_bind C1 C2
    aesop

lemma rule_cons {α β : Type}
  {C : α → M β}
  {P₁ P₂ : @hyperassertion M _ _ α}
  {Q : @hyperassertion M _ _ β}
  (h1 : triple P₂ C Q)
  (h2 : ∀ S, P₁ S → P₂ S) :
  triple P₁ C Q
  := by
    simp [triple_equiv] at *
    have h := WP_cons C Q
    aesop

end HHL

end
