import MonadicHHL.HHLMonads

-- with OK
-- Maybe I need a "replace element" function?

class HHLWithVal (M : Type _ → Type _) [Monad M] extends HHL M where

  getVal {α : Type _} (σ : HHL.elemType M α) : Option α
  mapElem {α β : Type _} (f : α → β) : HHL.elemType M α → HHL.elemType M β
  coerce {α β : Type _} (σ : HHL.elemType M α) (h : (getVal σ).isNone) : HHL.elemType M β

class HHLWithValLawful (M : Type _ → Type _) [Monad M] extends HHLWithVal M where
  -- Properties
  /-
  getVal_mapElem {α β : Type _} (f : α → β) (σ : HHL.elemType M α) :
    getVal (mapElem f σ) = Option.map f (getVal σ)
  -/
  -- mapElem behaves like a map, we could have more properties, but unsure if needed
  -- Let's see what other properties we need
  -- Why do we even need this one?

  inactive {α β : Type _} (C : α → M β) (σ : HHL.elemType M α) (σ' : HHL.elemType M β) :
    (h : (getVal σ).isNone) → (HHL.relWith C σ σ' ↔ σ' = coerce σ h)

  -- Value matters when ok
  active_congr {α β : Type _} (σ : HHL.elemType M α) (v : α)
      (h : getVal σ = some v) (C D : α → M β) (σ' : HHL.elemType M β) :
    C v = D v → (HHL.relWith C σ σ' ↔ HHL.relWith D σ σ')

open HHLWithVal
open HHLWithValLawful

section

variable {M : Type _ → Type _} [Monad M] [HHLWithValLawful M]

abbrev isOk {α : Type _} (σ : HHL.elemType M α) : Prop :=
    (getVal σ).isSome

abbrev isDead {α : Type _} (σ : HHL.elemType M α) : Prop :=
    (getVal σ).isNone


lemma inactive_congr {α β : Type _} (σ : HHL.elemType M α)
      (C D : α → M β) (σ' : HHL.elemType M β) (h : isDead σ) :
    (HHL.relWith C σ σ' ↔ HHL.relWith D σ σ') := by
    have h1 := inactive C σ σ' h
    have h2 := inactive D σ σ' h
    aesop

lemma relWith_congr {α β : Type _}
  {C1 C2 : α → M β}
  (h : ∀ v, C1 v = C2 v)
  (p : HHL.elemType M α) (p' : HHL.elemType M β) :
  HHL.relWith C1 p p' ↔ HHL.relWith C2 p p'
  := by
    cases hv : getVal p
    {
      have h := inactive_congr p C1 C2 p'
      aesop
    }
    {
      have h := active_congr _ _ hv C1 C2
      aesop
    }

lemma simplify_if_ok_relWith {α β : Type _}
  (b : α → Bool) (C₁ C₂ : α → M β)
  (σ : HHL.elemType M α) (σ' : HHL.elemType M β)
  {v : α} (h : getVal σ = some v)
  : HHL.relWith (fun x ↦ if b x then C₁ x else C₂ x) σ σ'
  ↔ if b v then HHL.relWith C₁ σ σ' else HHL.relWith C₂ σ σ'
:= by
  have h := active_congr _ _ h (fun x ↦ if b x then C₁ x else C₂ x)
  aesop

-- set_option linter.style.setOption false
-- set_option pp.universes true

def H.forallOk {α : Type _}
  (P : HHL.elemType M α × α → HHL.hyperassertion (M := M) α) : HHL.hyperassertion (M := M) α :=
    fun S => ∀ σ ∈ S, ∀v, getVal σ = some v → P (σ, v) S

def H.pure {α : Type _} (P : Prop) : HHL.hyperassertion (M := M) α :=
  fun _ => P

def Low {α : Type _} (b : α → Bool) : HHL.hyperassertion (M := M) α :=
    H.forallOk (fun p₁ => H.forallOk (fun p₂ => H.pure (b p₁.2 = b p₂.2)))

lemma low_elim {α : Type _}
  (b : α → Bool) (S : Set (HHL.elemType M α)) (h : Low b S) :
    H.forallOk (fun p => H.pure (b p.2)) S ∨ H.forallOk (fun p => H.pure (¬ (b p.2))) S
  := by
    simp [Low, H.forallOk, H.pure] at *
    grind

-- set_option diagnostics true

lemma low_semify_if {α : Type _}
  (b : α → Bool)
  (S : Set (HHL.elemType M α))
  (h : Low b S)
  {β : Type _}
  (C₁ C₂ : α → M β)
  :
(HHL.semify (fun x ↦ if b x then C₁ x else C₂ x) S
= HHL.semify C₁ S)
∨
(HHL.semify (fun x ↦ if b x then C₁ x else C₂ x) S
= HHL.semify C₂ S)
:= by
  -- have h := low_elim b S h
  have h := low_elim b S h
  simp [HHL.semify]
  cases h
  {
    rename_i h_true
    apply Or.inl
    apply Set.ext
    intro p'
    simp
    have h := simplify_if_ok_relWith b C₁ C₂
    have hh : ∀ p p', p ∈ S → (HHL.relWith (fun x ↦ if b x then C₁ x else C₂ x) p p'
            ↔ HHL.relWith C₁ p p') := by
      intro p p' hpS
      cases hp : getVal p
      {
        have h1 := inactive_congr p C₁ (fun x ↦ if b x = true then C₁ x else C₂ x) p'
        aesop
      }
      {
        rename_i pp v
        specialize h p p' (by aesop)
        simp [H.forallOk, H.pure] at h_true
        specialize h_true p hpS v hp
        simp [h_true] at h
        exact h
      }
    grind
  }
  {
    rename_i h_false
    apply Or.inr
    apply Set.ext
    intro p'
    simp
    have h := simplify_if_ok_relWith b C₁ C₂
    have hh : ∀ p p', p ∈ S → (HHL.relWith (fun x ↦ if b x then C₁ x else C₂ x) p p'
            ↔ HHL.relWith C₂ p p') := by
      intro p p' hpS
      cases hp : getVal p
      {
        have h1 := inactive_congr p C₂ (fun x ↦ if b x = true then C₁ x else C₂ x) p'
        aesop
      }
      {
        rename_i pp v
        specialize h p p' (by aesop)
        simp [H.forallOk, H.pure] at h_false
        specialize h_false p hpS v hp
        simp [h_false] at h
        exact h
      }
    grind
  }

lemma if_sync {M : Type _ → Type _} [Monad M] [HHLWithValLawful M]
  {α β : Type _} (b : α → Bool) (C₁ C₂ : α → M β)
  (P : HHL.hyperassertion α)
  (Q : HHL.hyperassertion β)
  (h : ∀ S, P S → Low b S)
  (h₁ : HHL.triple P C₁ Q)
  (h₂ : HHL.triple P C₂ Q) :
  HHL.triple P (fun x => if b x then C₁ x else C₂ x) Q := by
  simp [HHL.triple] at *
  intro S hP
  specialize h₁ S hP
  specialize h₂ S hP
  have hh := low_semify_if b S (h S hP) C₁ C₂
  aesop

/-
def dAnd (P : Prop) (Q : P → Prop) : Prop
  := P ∧ ((h : P) → Q h)

open Classical in
noncomputable def diteClassical {α : Sort _} (P : Prop)
    (t : P → α) (f : ¬ P → α) : α :=
  by
    classical
    by_cases h : P
    · exact t h
    · exact f h
-/


-- Other classes

class HHLPrecise (M : Type _ → Type _) [Monad M] extends HHLWithVal M where
  alwaysOutcome {α β : Type _} (C : α → M β) (σ : HHL.elemType M α) :
    ∃σ', HHL.relWith C σ σ'

/-
Everything satisfies this class except Set...
Because Set losing info with divergence... (empty set)
Allows framing!
-/

/-
Other class:
OkType
ErrType
NonTermType

Props that:
- OkType is the only Ok one
- The two others are dead
- We only have these 3 types
- Can quantify over those
- Hopefully, we can even connect the NonTerm type to loop divergence generically
-/

end
