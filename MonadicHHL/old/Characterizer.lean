import MonadicHHL.HHLMonads
import Smt
import Auto

open Lean
--- Characterizer definition


-- For the simplest case : Set α → Set β
structure charact_path (α β : Type _) where
  pc : α → Bool -- or Bool?
  res : α → β

abbrev characterizer (α β : Type _) : Type := List (charact_path α β)

--- Characterizer soundness


def characterizer_sound {α β : Type _}
  (C : α → Id β) (charac : characterizer α β) : Prop :=
  ∀a b, b = C a ↔ (∃ cp ∈ charac, cp.pc a ∧ cp.res a = b)



lemma characterizer_soundE {α β : Type _}
  {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (a : α) :
   ∃ cp ∈ charac, cp.pc a ∧ cp.res a = C a :=
  by
    simp [characterizer_sound] at h
    specialize h a (C a)
    aesop

lemma characterizer_sound_altE {α β : Type _}
  {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (cp : charact_path α β)
  (a : α) (b : β)
  (hh : cp ∈ charac ∧ cp.pc a ∧ cp.res a = b) :
  b = C a
  :=
  by
    simp [characterizer_sound] at h
    have h := (h a b).mpr
    simp at h
    specialize h cp
    aesop

lemma characterizer_sound_set_view {α β : Type _}
  {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (S : Set α) :
  C '' S = { σ' | ∃σ ∈ S, ∃ cp ∈ charac, cp.pc σ ∧ cp.res σ = σ' }
  := by
    apply Set.ext
    intro σ'
    simp [Set.image]
    apply Iff.intro
    {
      intro h
      rcases h with ⟨σ, inS, hC⟩
      have hcp := characterizer_soundE h σ
      rcases hcp with ⟨cp, cp_in, cp_pc, cp_res⟩
      apply Exists.intro σ
      simp [inS]
      apply Exists.intro cp
      simp [cp_in, cp_pc, cp_res, hC]
    }
    {
      intro h
      rcases h with ⟨σ, inS, ⟨cp, cp_in, cp_pc, cp_res⟩⟩
      have hC := characterizer_sound_altE h cp σ (cp.res σ)
      apply Exists.intro σ
      simp [inS]
      aesop
    }


------ Sound characterizers for pure, bind, if ------

@[charact_simps]
def Characterizer.pure {α β : Type _} (x : β) : characterizer α β :=
  [ {
      pc := fun _ => true,
      res := fun _ => x
  } ]

lemma characterizer_sound_id {α β : Type _} (x : β) :
  characterizer_sound (fun (_ : α) => pure x) (Characterizer.pure x) := by
  simp [characterizer_sound, Characterizer.pure]
  aesop

@[charact_simps]
def combine_characts {α β γ : Type _}
  (cps : charact_path α β × charact_path β γ) : charact_path α γ :=
  {
    pc := fun a => cps.1.pc a ∧ cps.2.pc (cps.1.res a),
    res := fun a => cps.2.res (cps.1.res a)
  }

@[charact_simps]
def Characterizer.bind {α β γ : Type _}
  (charac1 : characterizer α β)
  (charac2 : characterizer β γ) : characterizer α γ :=
  List.map combine_characts (List.product charac1 charac2)

lemma bind_characterizers_sound {α β γ : Type _}
  {C1 : α → Id β} {C2 : β → Id γ}
  {charac1 : characterizer α β}
  {charac2 : characterizer β γ}
  (h1 : characterizer_sound C1 charac1)
  (h2 : characterizer_sound C2 charac2) :
  characterizer_sound (fun v => C1 v >>= C2) (Characterizer.bind charac1 charac2) := by
  simp [characterizer_sound, Characterizer.bind, combine_characts, Bind.bind]
  intro a b
  apply Iff.intro
  {
    intro h
    have h1 := characterizer_soundE h1 a
    have h2 := characterizer_soundE h2 (C1 a)
    aesop
  }
  {
    intro h
    rcases h with ⟨cp1, cps, hcp_in, hcp_comb_res⟩
    sorry
    /-
    have h1 := characterizer_sound_altE h1 cp1 hcp1_in
    have h2 := characterizer_sound_altE h2 cp2 hcp2_in
    aesop
    -/
  }

@[charact_simps]
def conjoin_pc {α β : Type _}
  (b : α → Bool)
  (charac : charact_path α β)
  : charact_path α β :=
  {
    pc := fun a => charac.pc a ∧ b a,
    res := charac.res
  }

@[charact_simps]
def Characterizer.ite {α β : Type _}
  (b : α → Bool)
  (charac1 : characterizer α β)
  (charac2 : characterizer α β) : characterizer α β :=
  List.map (conjoin_pc b) charac1 ++ List.map (conjoin_pc (fun a => !b a)) charac2

lemma concat_for_branch {α β : Type _}
  {C1 C2 : α → Id β}
  {charac1 charac2 : characterizer α β}
  {b : α → Bool}
  (h1 : characterizer_sound C1 charac1)
  (h2 : characterizer_sound C2 charac2) :
  characterizer_sound
    (fun v => if b v = true then C1 v else C2 v)
    (List.map (conjoin_pc b) charac1 ++ List.map (conjoin_pc (fun a => !b a)) charac2) := by
  simp [characterizer_sound, conjoin_pc]
  intro x y

  apply Iff.intro
  {
    have h1 := characterizer_soundE h1 x
    have h2 := characterizer_soundE h2 x
    aesop
  }
  {
    intro h
    rcases h with ⟨cp, hcp_in, hcp_pc, hcp_res⟩
    cases hcp_in
    {
      rename_i cp_in
      rcases cp_in with ⟨cp, cp_in_charac1, hpc_conj⟩
      have h := characterizer_sound_altE h1 cp x y
      aesop
    }
    {
      rename_i cp_in
      rcases cp_in with ⟨cp, cp_in_charac1, hpc_conj⟩
      rename_i cp'
      have h := characterizer_sound_altE h2 cp x y
      aesop
    }
  }

@[charact_simps]
def Characterizer.generic {α β : Type _}
  (C : α → Id β) : characterizer α β :=
  [{
    pc := fun _ => true,
    res := C
  }]

lemma generic_characterizer_sound {α β : Type _}
  (C : α → Id β) :
  characterizer_sound C (Characterizer.generic C) := by
  simp [characterizer_sound, Characterizer.generic]
  aesop




--------- WP from characterizers ------

def hyperassertion (α : Type _) := Set α → Prop

def triple {α β : Type _}
  (P : hyperassertion α) (C : α → Id β) (Q : hyperassertion β) : Prop :=
  ∀ S, P S → Q (C '' S)

def is_WP {α β : Type _}
  (C : α → Id β) (Q : hyperassertion β) (P : hyperassertion α) : Prop :=
  triple P C Q ∧
  (∀ P', triple P' C Q → (∀ S, P' S → P S))

lemma is_WP_unique {α β : Type _}
  (C : α → Id β) (Q : hyperassertion β)
  (P1 P2 : hyperassertion α)
  (h1 : is_WP C Q P1)
  (h2 : is_WP C Q P2) :
  P1 = P2 :=
  by
    apply Set.ext
    intro S
    simp [is_WP] at h1 h2
    aesop

lemma is_WP_obvious {α β : Type _}
  (C : α → Id β) (Q : hyperassertion β) :
  is_WP C Q (fun S => Q (C '' S))
  := by simp [is_WP, triple]

lemma is_WPE {α β : Type _}
  {P : hyperassertion α}
  {C : α → Id β}
  {Q : hyperassertion β}
  (h : is_WP C Q P)
: (∀ S, P S = Q (C '' S))
:= by
  have heq : P = (fun S => Q (C '' S)) := by
    apply is_WP_unique C Q _ _ h
    apply is_WP_obvious
  aesop

/-
def WP_forall_from_charact {α β : Type _}
  (charac : characterizer α β) (Q : β → Prop) : hyperassertion α :=
  fun S => ∀σ ∈ S, ∀ cp ∈ charac, cp.pc σ → Q (cp.res σ)

lemma WP_forall_from_charact_is_WP {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → Prop) :
  is_WP C (fun S => ∀σ ∈ S, Q σ) (WP_forall_from_charact charac Q) :=
  by
    constructor
    {
      intro S hP
      simp [WP_forall_from_charact] at hP
      simp [Set.image]
      intro a ha
      have hcp := characterizer_soundE h a
      rcases hcp with ⟨cp, cp_in, cp_pc, cp_res⟩
      specialize hP a ha cp cp_in cp_pc
      aesop
    }
    {
      intro P' htriple S hP
      simp [WP_forall_from_charact]
      intro σ hσ cp cp_in cp_pc
      have hcp := characterizer_sound_altE h cp σ (cp.res σ)
      aesop
    }

def WP_exists_from_charact {α β : Type _}
  (charac : characterizer α β) (Q : β → Prop) : hyperassertion α :=
  fun S => ∃σ ∈ S, ∃ cp ∈ charac, cp.pc σ ∧ Q (cp.res σ)

lemma WP_exists_from_charact_is_WP {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → Prop) :
  is_WP C (fun S => ∃σ ∈ S, Q σ) (WP_exists_from_charact charac Q) :=
  by
    constructor
    {
      intro S hP
      simp [WP_exists_from_charact] at hP
      simp [Set.image]
      rcases hP with ⟨σ, inS, ⟨cp, hcp⟩⟩
      apply Exists.intro σ
      simp [inS]
      have hcp' := characterizer_sound_altE h cp σ (cp.res σ)
      aesop
    }
    {
      intro P' htriple S hP
      simp [WP_exists_from_charact]
      simp [triple] at htriple
      specialize htriple S hP
      rcases htriple with ⟨σ, inS, hh⟩
      apply Exists.intro σ
      simp [inS]
      have hcp := characterizer_soundE h σ
      aesop
    }
-/

--- "Constructors"

@[wp_simps]
def H.pure {α : Type _} (P : Prop) : hyperassertion α :=
  fun _ => P

@[wp_simps]
def H.forall {α : Type _} (P : α → hyperassertion α) : hyperassertion α :=
  fun S => ∀ σ ∈ S, P σ S

@[wp_simps]
def H.exists {α : Type _} (P : α → hyperassertion α) : hyperassertion α :=
  fun S => ∃ σ ∈ S, P σ S

---- Example

abbrev forall_forall_post {β : Type _} (Q : β → β → Prop) : hyperassertion β :=
  H.forall (fun σ1 => H.forall (fun σ2 => H.pure (Q σ1 σ2)))

@[wp_simps]
def conjoin_all {α : Type _} : List (hyperassertion α) → hyperassertion α
  | List.nil => fun _ => true
  | cp :: rest =>
    fun S => cp S ∧ conjoin_all rest S

@[wp_simps]
def WP.forall {α β : Type _}
  (charac : characterizer α β) (P : β → hyperassertion α) : hyperassertion α :=
  fun S =>
    ∀ σ ∈ S,
      List.foldl
        (fun acc cp =>
          acc ∧ (cp.pc σ → P (cp.res σ) S))
        true
        charac
  /-
    conjoin_all
      (List.map
        (fun cp =>
          fun S =>
            ∀ σ ∈ S, cp.pc σ → P (cp.res σ) S)
        charac)
        -/
/-
  fun S =>
    -- ∀ σ ∈ S, List.all (List.map (fun cp => cp.pc σ → P (cp.res σ) S) charac)
--      (fun acc cp => acc ∧ (cp.pc σ → P (cp.res σ) S))
    ∀ σ ∈ S, ∀ cp ∈ charac, cp.pc σ → P (cp.res σ) S
  -/

lemma WP.forall_eq {α β : Type _} (charac : characterizer α β) (P : β → hyperassertion α) :
  WP.forall charac P =
  fun S =>
    ∀ σ ∈ S, ∀ cp ∈ charac, cp.pc σ → P (cp.res σ) S
  := by
    apply funext
    intro S
    simp [WP.forall]
    sorry

@[wp_simps]
def WP.exists {α β : Type _}
  (charac : characterizer α β) (P : β → hyperassertion α) : hyperassertion α :=
  fun S =>
    ∃ σ ∈ S, ∃ cp ∈ charac, cp.pc σ ∧ P (cp.res σ) S

lemma triple_cons_post {α β : Type _}
  (P : hyperassertion α)
  (C : α → Id β)
  (Q Q' : hyperassertion β)
  (htriple : triple P C Q')
  (hcons : ∀ S, Q' S → Q S)
  : triple P C Q :=
  by
    simp [triple] at *
    aesop

@[grind]
lemma is_WP_forall_comp {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → hyperassertion β)
  (P : β → hyperassertion α)
  (hh : ∀ σ', is_WP C (Q σ') (P σ')) :
  is_WP C (H.forall Q) (WP.forall charac P) := by
    have heq : WP.forall charac P = (fun S => H.forall Q (C '' S)) := by
    {
      apply funext
      intro S
      simp [WP.forall_eq, H.forall]
      have hsimpler : ∀ σ ∈ S, (∀ cp ∈ charac, cp.pc σ → P (cp.res σ) S) ↔ (Q (C σ) (C '' S)) := by
      {
        intro σ hS
        apply Iff.intro
        {
          intro hcp
          have hh := is_WPE (hh (C σ)) S
          rw [hh.symm]
          have h := characterizer_soundE h σ
          rcases h with ⟨cp, cp_in, cp_pc, cp_res⟩
          specialize hcp cp cp_in cp_pc
          aesop
        }
        {
          intro hQ cp cp_in cp_pc
          have hh := is_WPE (hh (C σ)) S
          have hcp := characterizer_sound_altE h cp σ (cp.res σ)
          aesop
        }
      }
      aesop
    }
    rw [heq]
    apply is_WP_obvious

@[grind]
lemma is_WP_exists_comp {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → hyperassertion β)
  (P : β → hyperassertion α)
  (hh : ∀ σ', is_WP C (Q σ') (P σ')) :
  is_WP C (H.exists Q) (WP.exists charac P) := by
    have heq : WP.exists charac P = (fun S => H.exists Q (C '' S)) := by
    {
      apply funext
      intro S
      simp [WP.exists, H.exists]
      have hsimpler : ∀ σ ∈ S, (∃ cp ∈ charac, cp.pc σ ∧ P (cp.res σ) S) ↔ (Q (C σ) (C '' S)) := by
        {
          intro σ hS
          apply Iff.intro
          {
            intro hcp
            rcases hcp with ⟨cp, cp_in, cp_pc, cp_res⟩
            have hh := is_WPE (hh (C σ)) S
            have h := characterizer_sound_altE h cp σ
            aesop
          }
          {
            intro hQ
            have hcp := characterizer_soundE h σ
            have hh := is_WPE (hh (C σ)) S
            aesop
          }
        }
      grind
    }
    rw [heq]
    apply is_WP_obvious


@[simp, grind]
lemma is_WP_pure {α β : Type _} {C : α → Id β} (P : Prop)
  : is_WP C (H.pure P) (H.pure P)
  := by simp [is_WP, triple, H.pure]

lemma elim_triple {α β : Type _}
  {P : hyperassertion α}
  {C : α → Id β}
  {Q : hyperassertion β}
  (htriple : triple P C Q)
  (S : Set α)
  (hP : P S) :
  Q (C '' S) :=
  by
    simp [triple] at htriple
    specialize htriple S hP
    aesop

-- @[grind .]
lemma is_WP_and {α β : Type _} {C : α → Id β}
  {P1 P2 : hyperassertion α}
  {Q1 Q2 : hyperassertion β}
  (h1 : is_WP C Q1 P1)
  (h2 : is_WP C Q2 P2) :
  is_WP C (fun S => Q1 S ∧ Q2 S) (fun S => P1 S ∧ P2 S) :=
  by
    have h1 := is_WPE h1
    have h2 := is_WPE h2
    simp [is_WP, triple]
    aesop

-- @[grind .]
lemma is_WP_or {α β : Type _} {C : α → Id β}
  {P1 P2 : hyperassertion α}
  {Q1 Q2 : hyperassertion β}
  (h1 : is_WP C Q1 P1)
  (h2 : is_WP C Q2 P2) :
  is_WP C (fun S => Q1 S ∨ Q2 S) (fun S => P1 S ∨ P2 S) :=
  by
    have h1 := is_WPE h1
    have h2 := is_WPE h2
    simp [is_WP, triple]
    aesop

lemma is_WP_forall_normal {α β γ : Type _} {C : α → Id β}
  (Q : γ → hyperassertion β)
  (P : γ → hyperassertion α)
  (hh : ∀ x, is_WP C (Q x) (P x)) :
  is_WP C (fun S => ∀ x, Q x S) (fun S => ∀ x, P x S) := by
    constructor
    {
      intro S h x
      have hh := is_WPE (hh x) S
      aesop
    }
    {
      intro P' htriple S hP x
      have hh := is_WPE (hh x) S
      aesop
    }

lemma is_WP_exists_normal {α β γ : Type _} {C : α → Id β}
  (Q : γ → hyperassertion β)
  (P : γ → hyperassertion α)
  (hh : ∀ x, is_WP C (Q x) (P x)) :
  is_WP C (fun S => ∃ x, Q x S) (fun S => ∃ x, P x S) := by
    constructor
    {
      simp [triple]
      intro S x
      have hh := is_WPE (hh x)
      aesop
    }
    {
      intro P' htriple S hP
      have htriple := elim_triple htriple S hP
      rcases htriple with ⟨x, h'⟩
      have hh := is_WPE (hh x) S
      aesop
    }






--------------------------
-- Examples
--------------------------

-- Forall

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → Prop) :
  is_WP C
    (H.forall (fun σ => H.pure (Q σ)))
    (WP.forall charac (fun σ => H.pure (Q σ)))
  := by grind

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → β → Prop) :
  is_WP C
    (H.forall (fun σ1 => H.forall (fun σ2 => H.pure (Q σ1 σ2))))
    (WP.forall charac (fun σ1 => WP.forall charac (fun σ2 => H.pure (Q σ1 σ2))))
  := by grind

-- Exists

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → Prop) :
  is_WP C
    (H.exists (fun σ => H.pure (Q σ)))
    (WP.exists charac (fun σ => H.pure (Q σ)))
  := by grind

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → β → Prop) :
  is_WP C
    (H.exists (fun σ1 => H.exists (fun σ2 => H.pure (Q σ1 σ2))))
    (WP.exists charac (fun σ1 => WP.exists charac (fun σ2 => H.pure (Q σ1 σ2))))
  := by grind

-- Mixed

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → β → Prop) :
  is_WP C
    (H.forall (fun σ1 => H.exists (fun σ2 => H.pure (Q σ1 σ2))))
    (WP.forall charac (fun σ1 => WP.exists charac (fun σ2 => H.pure (Q σ1 σ2))))
  := by grind

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → β → Prop) :
  is_WP C
    (H.exists (fun σ1 => H.forall (fun σ2 => H.pure (Q σ1 σ2))))
    (WP.exists charac (fun σ1 => WP.forall charac (fun σ2 => H.pure (Q σ1 σ2))))
  := by grind


/-

def WP_forall_forall_from_charact {α β : Type _}
  (charac : characterizer α β) (Q : β → β → Prop) : hyperassertion α :=
  fun S =>
    ∀ a1 ∈ S, ∀cp1 ∈ charac, cp1.pc a1 →
    ∀ a2 ∈ S, ∀cp2 ∈ charac, cp2.pc a2 →
      Q (cp1.res a1) (cp2.res a2)

lemma same_hyperassertions {β : Type _} (Q : β → β → Prop) :
  (fun S => ∀σ1 ∈ S, ∀σ2 ∈ S, Q σ1 σ2) = forall_forall_post Q
  := rfl

lemma WP_forall_forall_from_charact_sound {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → β → Prop) :
  is_WP C
    -- (forall_forall_post Q)
    (fun S => ∀σ1 ∈ S, ∀σ2 ∈ S, Q σ1 σ2)
    (WP_forall_forall_from_charact charac Q) :=
  by
    constructor
    {
      simp [triple, WP_forall_forall_from_charact, Set.image]
      intro S hP σ1 h1 σ2 h2
      have hcp1 := characterizer_soundE h σ1
      rcases hcp1 with ⟨cp1, cp1_in, cp1_pc, cp1_res⟩
      have hcp2 := characterizer_soundE h σ2
      rcases hcp2 with ⟨cp2, cp2_in, cp2_pc, cp2_res⟩
      specialize hP σ1 h1 cp1 cp1_in cp1_pc σ2 h2 cp2 cp2_in cp2_pc
      aesop
    }
    {
      intro P' htriple S hP
      simp [WP_forall_forall_from_charact]
      intro σ1 h1 cp1 cp1_in cp1_pc σ2 h2 cp2 cp2_in cp2_pc
      have hcp1 := characterizer_sound_altE h cp1 σ1 (cp1.res σ1)
      have hcp2 := characterizer_sound_altE h cp2 σ2 (cp2.res σ2)
      specialize htriple S hP
      aesop
    }

lemma WP_forall_forall_same {α β : Type _}
  (charac : characterizer α β) (Q : β → β → Prop) :
  WP_forall_forall_from_charact charac Q = WP_forall_forall_from_charact_comp charac Q
  := rfl

-/


/-
open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

partial def computeWP_from_charact {α β : Type _}
  (charac : characterizer α β)
  (Q : hyperassertion β) : TacticM (Expr) :=
  do
    let wp_expr ← mkAppM ``WP.forall #[mkConst ``α, mkConst ``β, mkQuotedExpr charac, mkLambda `σ BinderInfo.default (mkConst ``β) (mkAppM ``H.pure #[mkAppM ``Q #[mkVar `σ]])]
    return wp_expr

partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext
    (do
       let target ← getMainTarget
       let P ← inferType hP
       let eq ← isDefEq P target
       if eq then
         let goal ← getMainGoal
         MVarId.assign goal hP
         return true
       else
         match Expr.and? P with
         | Option.none        => return false
         | Option.some (Q, R) =>
           let hQ ← mkAppM ``And.left #[hP]
           let success ← destructAndExpr hQ
           if success then
             return true
           else
             let hR ← mkAppM ``And.right #[hP]
             destructAndExpr hR)
-/


structure CharGen {α β : Type _} (C : α → Id β) where
  charact : characterizer α β
  soundness : characterizer_sound C charact

@[charact_simps]
def CharGen.default {α β : Type _} (C : α → Id β) : CharGen C :=
  {
    charact := Characterizer.generic C,
    soundness := generic_characterizer_sound C
  }

@[charact_simps]
def CharGen.bind {α β γ : Type _}
  {C1 : α → Id β} {C2 : β → Id γ}
  (cg1 : CharGen C1)
  (cg2 : CharGen C2) : CharGen (fun v => C1 v >>= C2) :=
  {
    charact := Characterizer.bind cg1.charact cg2.charact,
    soundness := bind_characterizers_sound cg1.soundness cg2.soundness
  }

@[charact_simps]
def CharGen.bind' {α β γ : Type _}
  {C1 : α → Id β} {C2 : β → Id γ} {C : α → Id γ}
  (h : C = C1 >=> C2)
  (cg1 : CharGen C1)
  (cg2 : CharGen C2)
  : CharGen C :=
  {
    charact := Characterizer.bind cg1.charact cg2.charact,
    soundness := by
      have hh := bind_characterizers_sound cg1.soundness cg2.soundness
      have heq : C = (fun v => C1 v >>= C2) := by
        apply funext
        intro v
        rw [h]
        aesop
      aesop
  }

@[charact_simps]
def CharGen.ite {α β : Type _} {C1 C2 : α → Id β} (b : α → Bool)
  (cg1 : CharGen C1) (cg2 : CharGen C2)
  : CharGen (fun v => if b v then C1 v else C2 v) :=
  {
    charact := Characterizer.ite b cg1.charact cg2.charact,
    soundness := concat_for_branch cg1.soundness cg2.soundness
  }

@[charact_simps]
def CharGen.ite' {α β : Type _} (C : α → Id β) (b : α → Bool)
  (C1 C2 : α → Id β)
  (h : ∀ v, C v = if b v then C1 v else C2 v)
  (cg1 : CharGen C1) (cg2 : CharGen C2) : CharGen C :=
  {
    charact := Characterizer.ite b cg1.charact cg2.charact,
    soundness := by
      -- rewrite the program using h and reuse concat_for_branch
      have hfun : C = (fun v => if b v then C1 v else C2 v) := by
        funext v
        simpa using h v
      simpa [hfun] using concat_for_branch cg1.soundness cg2.soundness
  }

@[charact_simps]
def CharGen.pure {α β : Type _} (C : α → Id β) (x : β)
  (h : C = (fun _ => return x)) : CharGen C :=
  {
    charact := Characterizer.pure x,
    soundness := by
      simp [characterizer_sound, Characterizer.pure, h]
      aesop
  }

-- transport a CharGen across an equality of programs
@[charact_simps]
def CharGen.congr {α β : Type _} {C C' : α → Id β}
    (h : C = C') (cg : CharGen C) : CharGen C' :=
{
  charact := cg.charact
  soundness := by
    -- rewrite the goal's C' back to C and reuse cg.soundness
    simpa [h] using cg.soundness
}

-- goal classifiers
open Lean Elab Tactic

def Lean.MVarId.isCharGenGoal : MVarId → TacticM Bool
| mvarId => do
  let goalType <- mvarId.getType
  let_expr CharGen _ _ _ := goalType | return false
  return true

@[charact_simps]
def CharGen.iteProp {α β : Type _}
    {p : α → Prop} [DecidablePred p]
    {C1 C2 : α → Id β}
    (cg1 : CharGen C1) (cg2 : CharGen C2) :
    CharGen (fun v => if p v then C1 v else C2 v) :=
by
  -- Bool-form characterizer
  have cg0 :
      CharGen (fun v => if decide (p v) = true then C1 v else C2 v) :=
    CharGen.ite (b := fun v => decide (p v)) cg1 cg2

  -- convert Bool-if (= true) to Prop-if
  refine CharGen.congr (C := fun v => if decide (p v) = true then C1 v else C2 v)
                       (C' := fun v => if p v then C1 v else C2 v)
                       ?_ cg0
  funext v
  simp


structure WPGen {α β : Type _}
 (C : α → Id β) (sound_charact : CharGen C) (Q : hyperassertion β)
 where
  P : hyperassertion α
  is_WP : is_WP C Q P

-- goal classifier for WPGen
open Lean Elab Tactic in
def Lean.MVarId.isWPGenGoal : MVarId → TacticM Bool
| mvarId => do
  let goalType <- mvarId.getType
  let_expr WPGen _ _ _ := goalType | return false
  return true

@[wp_simps]
def WPGen.default {α β : Type _}
  (C : α → Id β) (cg : CharGen C) (Q : hyperassertion β) : WPGen C cg Q :=
  {
    P := fun S => Q (C '' S),
    is_WP := is_WP_obvious C Q
  }

@[wp_simps]
def WPGen.and {α β : Type _}
  (C : α → Id β) (cg : CharGen C) (Q1 Q2 : hyperassertion β)
  (wp1 : WPGen C cg Q1) (wp2 : WPGen C cg Q2)
  : WPGen C cg (fun S => Q1 S ∧ Q2 S) :=
  {
    P := fun S => wp1.P S ∧ wp2.P S,
    is_WP := is_WP_and wp1.is_WP wp2.is_WP
  }

@[wp_simps]
def WPGen.or {α β : Type _}
  (C : α → Id β) (cg : CharGen C) (Q1 Q2 : hyperassertion β)
  (wp1 : WPGen C cg Q1) (wp2 : WPGen C cg Q2)
  : WPGen C cg (fun S => Q1 S ∨ Q2 S) :=
  {
    P := fun S => wp1.P S ∨ wp2.P S,
    is_WP := is_WP_or wp1.is_WP wp2.is_WP
  }

@[wp_simps]
def WPGen.pure {α β : Type _}
  (C : α → Id β) (cg : CharGen C) (P : Prop)
  : WPGen C cg (H.pure P) :=
  {
    P := H.pure P,
    is_WP := is_WP_pure P
  }

@[wp_simps]
def WPGen.forallState {α β : Type _}
  (C : α → Id β) (cg : CharGen C) (Q : β → hyperassertion β)
  (hh : ∀ σ', WPGen C cg (Q σ')) :
  WPGen C cg (H.forall Q) :=
  {
    P := WP.forall cg.charact (fun σ => (hh σ).P),
    is_WP := is_WP_forall_comp cg.soundness Q (fun σ => (hh σ).P) (fun σ => (hh σ).is_WP)
  }

@[wp_simps]
def WPGen.existsState {α β : Type _}
  (C : α → Id β) (cg : CharGen C) (Q : β → hyperassertion β)
  (hh : ∀ σ', WPGen C cg (Q σ')) :
  WPGen C cg (H.exists Q) :=
  {
    P := WP.exists cg.charact (fun σ => (hh σ).P),
    is_WP := is_WP_exists_comp cg.soundness Q (fun σ => (hh σ).P) (fun σ => (hh σ).is_WP)
  }

@[wp_simps]
def WPGen.forall_normal {α β γ : Type _}
  (C : α → Id β) (cg : CharGen C)
  (Q : γ → hyperassertion β)
  (hh : ∀ x, WPGen C cg (Q x)) :
  WPGen C cg (fun S => ∀ x, Q x S) :=
  {
    P := fun S => ∀ x, (hh x).P S,
    is_WP := by
      apply is_WP_forall_normal Q
      intro x
      exact (hh x).is_WP
  }

@[wp_simps]
def WPGen.exists_normal {α β γ : Type _}
  (C : α → Id β) (cg : CharGen C)
  (Q : γ → hyperassertion β)
  (hh : ∀ x, WPGen C cg (Q x)) :
  WPGen C cg (fun S => ∃ x, Q x S) :=
  {
    P := fun S => ∃ x, (hh x).P S,
    is_WP := by
      apply is_WP_exists_normal Q
      intro x
      exact (hh x).is_WP
  }

lemma WPGen.intro {α β : Type _}
  {C : α → Id β}
  {P : hyperassertion α}
  {Q : hyperassertion β}
  (sg : CharGen C)
  (wp : WPGen C sg Q)
  (h : ∀ S, P S → wp.P S)
: triple P C Q :=
  by
    simp [triple]
    intro S hP
    have hwp := elim_triple (wp.is_WP).left S (h S hP)
    aesop

@[charact_simps]
def CharGen.pure' {α β : Type _} {C : α → Id β} (f : α → β)
  (h : C = (fun x => return f x)) : CharGen C :=
  {
    charact := Characterizer.generic f,
    soundness := by
      simp [characterizer_sound, Characterizer.generic, h]
      aesop
  }

def same : Int → Int := fun x =>
  x

def neg : Int → Int := fun x =>
  -x

-- Test example: simple conditional computation
def abs : Int → Id Int := fun x => do
  if x > 0 then
    return (same x)
  else
    return (neg x)

def pre_abs : hyperassertion Int :=
  H.forall (fun x1 => H.forall (fun x2 => H.pure (x1 = x2 || x1 = -x2)))

def post_abs : hyperassertion Int :=
  H.forall (fun y1 => H.forall (fun y2 => H.pure (y1 = y2)))

lemma abs_satisfies_triple : triple pre_abs abs post_abs := by
  apply WPGen.intro
  rotate_left
  {
    apply CharGen.iteProp
    · apply CharGen.pure' _ rfl
    · apply CharGen.pure' _ rfl
  }
  {
    apply WPGen.forallState
    intro σ1
    apply WPGen.forallState
    intro σ2
    apply WPGen.pure
  }
  {
    intro S
    unfold pre_abs
    simp [charact_simps, wp_simps]
    unfold same neg
    grind
  }

def abs_twice : Int → Id Int := fun x => do
  let y ← abs x
  abs y

@[charact_simps]
lemma product_eq (l₁ : List α) (l₂ : List β) :
  List.product l₁ l₂ = l₁.flatMap fun a => l₂.map (Prod.mk a)
  := by rfl

@[simp]
lemma minus_minus_same (x : Int) :
  -(-x) = x :=
  by
    grind

lemma abs_with_bind_satisfies_triple : triple pre_abs abs_twice post_abs := by
  unfold abs_twice abs
  apply WPGen.intro
  rotate_left
  {
    apply CharGen.bind' rfl
    {
      apply CharGen.iteProp
      · apply CharGen.pure' _ rfl
      · apply CharGen.pure' _ rfl
    }
    {
      apply CharGen.iteProp
      · apply CharGen.pure' _ rfl
      · apply CharGen.pure' _ rfl
    }
  }
  {
    -- unfold CharGen.bind' Characterizer.bind combine_characts
    apply WPGen.forallState
    intro σ1
    apply WPGen.forallState
    intro σ2
    apply WPGen.pure
  }
  {
    intro S
    unfold pre_abs
    -- simp [wp_simps]
    simp [charact_simps, wp_simps]
    unfold same neg
    -- grind
    sorry
  }

lemma kleisli_seq
  {α β γ : Type _}
  (C1 : α → Id β)
  (C2 : β → Id γ)
  (S : Set α)
:
  (C1 >=> C2) '' S = C2 '' (C1 '' S) :=
  by
    simp [Set.image]
    aesop

lemma rule_seq
  (h1 : triple P C1 R)
  (h2 : triple R C2 Q) :
  triple P (C1 >=> C2) Q :=
  by
    simp [triple] at *
    intro S hP
    have hR := elim_triple h1 S hP
    have hQ := elim_triple h2 (C1 '' S) hR
    rw [kleisli_seq C1 C2 S]
    aesop

lemma abs_with_bind_satisfies_triple_alt : triple pre_abs abs_twice post_abs := by
  unfold abs_twice
  apply rule_seq
  {
    exact abs_satisfies_triple
  }
  {
    apply WPGen.intro
    rotate_left
    {
      apply CharGen.iteProp
      · apply CharGen.pure' _ rfl
      · apply CharGen.pure' _ rfl
    }
    {
      apply WPGen.forallState
      intro σ1
      apply WPGen.forallState
      intro σ2
      apply WPGen.pure
    }
    {
      intro S
      unfold post_abs
      simp [charact_simps, wp_simps]
      unfold same neg
      grind
    }
  }

/- The following automation tactics live in the `Lean.Elab.Tactic` namespace. -/
open Lean Elab Tactic

/- Automation for `CharGen` goals. Tries `iteProp`, then `bind`, then `pure'`,
    otherwise falls back to `default`, recursing on subgoals. -/
partial def computeChar : TacticM Unit := do
  -- try iteProp
  try
    evalTactic (← `(tactic| refine CharGen.iteProp ?_ ?_))
    let gs ← getGoals
    for g in gs do
      setGoals [g]
      computeChar
    return
  catch _ => pure ()
  -- try bind
  try
    evalTactic (← `(tactic| refine CharGen.bind ?_ ?_))
    let gs ← getGoals
    for g in gs do
      setGoals [g]
      computeChar
    return
  catch _ => pure ()
  -- try pure
  try
    evalTactic (← `(tactic| refine CharGen.pure' _ rfl))
    return
  catch _ => pure ()
  -- default fallback
  try
    evalTactic (← `(tactic| apply CharGen.default))
  catch _ => pure ()

/-- Automation for `WPGen` goals. Tries structured constructors and recurses. -/
partial def computeWP : TacticM Unit := do
  -- First, if the goal is a forall, intro and recurse
  let tgt ← getMainTarget
  match tgt with
  | Expr.forallE _ _ _ _ =>
      try
        evalTactic (← `(tactic| intro))
        computeWP
        return
      catch _ => pure ()
  | _ => pure ()

  -- Normalize the goal type to help with matching
  let goal ← getMainGoal
  let goalType ← goal.getType
  let goalTypeNorm ← Meta.whnf goalType
  -- Check if the goal type is WPGen with H.forall postcondition
  let isForallPost := match goalTypeNorm with
    | Expr.app (Expr.app (Expr.app (Expr.const `WPGen _) _) _) post =>
        match post.getAppFn with
        | Expr.const `H.forall _ => true
        | _ => false
    | _ => false

  -- forallState
  if isForallPost then
    try
      evalTactic (← `(tactic| apply WPGen.forallState))
      let gs ← getGoals
      for g in gs do
        setGoals [g]
        computeWP
      return
    catch _ =>
      try
        evalTactic (← `(tactic| refine WPGen.forallState ?_ ?_ ?_ ?_))
        let gs ← getGoals
        for g in gs do
          setGoals [g]
          computeWP
        return
      catch _ => pure ()
  else
    -- Try apply/refine anyway (might work with type inference)
    try
      evalTactic (← `(tactic| apply WPGen.forallState))
      let gs ← getGoals
      for g in gs do
        setGoals [g]
        computeWP
      return
    catch _ =>
      try
        evalTactic (← `(tactic| refine WPGen.forallState ?_ ?_ ?_ ?_))
        let gs ← getGoals
        for g in gs do
          setGoals [g]
          computeWP
        return
      catch _ => pure ()
  -- existsState
  try
    evalTactic (← `(tactic| apply WPGen.existsState))
    let gs ← getGoals
    for g in gs do
      setGoals [g]
      computeWP
    return
  catch _ => pure ()
  -- and
  try
    evalTactic (← `(tactic| refine WPGen.and ?_ ?_ ?_ ?_ ?_))
    let gs ← getGoals
    for g in gs do
      setGoals [g]
      computeWP
    return
  catch _ => pure ()
  -- or
  try
    evalTactic (← `(tactic| refine WPGen.or ?_ ?_ ?_ ?_ ?_))
    let gs ← getGoals
    for g in gs do
      setGoals [g]
      computeWP
    return
  catch _ => pure ()
  -- pure
  try
    evalTactic (← `(tactic| apply WPGen.pure))
    return
  catch _ => pure ()
  -- default (catch-all, last)
  try
    evalTactic (← `(tactic| first | apply WPGen.default | refine WPGen.default ?_ ?_ ?_))
    return
  catch _ => pure ()

elab "compute_char" : tactic => computeChar
elab "compute_wp" : tactic => computeWP

elab "solve_triple" : tactic => do
  evalTactic (← `(tactic| refine WPGen.intro ?_ ?_ ?_))
  -- first solve all CharGen goals
  let gs0 ← getGoals
  let cgGoals ← gs0.filterM (·.isCharGenGoal)
  let rest0 ← gs0.filterM (fun g => do return !(← g.isCharGenGoal))
  let mut acc : List MVarId := []
  for g in cgGoals do
    setGoals [g]
    computeChar
    acc := acc ++ (← getGoals)
  setGoals (acc ++ rest0)

  -- then solve all WPGen goals recursively
  let mut done := false
  while !done do
    let gs ← getGoals
    let wpGoals ← gs.filterM (·.isWPGenGoal)
    if wpGoals.isEmpty then
      done := true
    else
      let rest ← gs.filterM (fun g => do return !(← g.isWPGenGoal))
      let mut newAcc : List MVarId := []
      for g in wpGoals do
        setGoals [g]
        computeWP
        newAcc := newAcc ++ (← getGoals)
      setGoals (newAcc ++ rest)



/-- Sanity check: the tactic `solve_triple` drives the proof, leaving only the
    final arithmetic/set-reasoning goal to the user. -/
example : triple pre_abs abs post_abs := by
  solve_triple
  -- Do not modify the part below, it should solve the goal
  intro S
  unfold post_abs
  simp [charact_simps, wp_simps]
  unfold same neg
  grind
