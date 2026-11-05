/-
# Nondeterminism transformer

* `NonDetT m`: the free nondeterminism transformer over a monad `m`
  (computations of `m`, plus `pickCont` choices that may also block).
* `HHLExtra`: the extra structure on `HHL m` needed to build `HHL (NonDetT m)`.
* `HHL (NonDetT m)`: a choice resolves per execution, and only reachable
  branches are followed.
* `NonDetT Id` has the same triples as `Set`, through its set semantics `NonDetT.sem`.
-/
import MonadicHHL.HHLMonads
import MonadicHHL.Instances.Id
import MonadicHHL.Instances.Set

section NonDeterministicTransformer

inductive NonDetT (m : Type _ -> Type _) : (α : Type _) -> Type _ where
  | pure {α} (ret : α) : NonDetT m α
  | vis {α} {β} (x : m β) (f : β → NonDetT m α) : NonDetT m α
  | pickCont {α} (τ : Type _) (p : τ -> Prop) (f : τ → NonDetT m α) : NonDetT m α

def NonDetT.bind {m : Type _ → Type _} {α β : Type _}
    (x : NonDetT m α) (f : α → NonDetT m β) : NonDetT m β :=
  match x with
  | pure ret => f ret
  | vis x f' => vis x fun y => bind (f' y) f
  | pickCont τ p f' => pickCont τ p fun t => bind (f' t) f

instance {m : Type _ → Type _} : Monad (NonDetT m) where
  pure := NonDetT.pure
  bind := NonDetT.bind

instance {m : Type _ → Type _} [Monad m] [LawfulMonad m] : LawfulMonad (NonDetT m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { introv; induction x
    <;> simp [Functor.map, NonDetT.bind]
    <;> solve_by_elim [funext] }
  { introv; simp [bind, NonDetT.bind] }
  introv; induction x
  <;> simp [bind, NonDetT.bind]
  <;> solve_by_elim [funext]

end NonDeterministicTransformer

open HHL

/-! ## Extra structure on the base monad -/

/-- Extra structure on an `HHL` monad needed to build `HHL (NonDetT m)`.
An element is *active* when it carries a value (`getVal p = some v`) and
*inactive* otherwise (e.g. an exception state); inactive elements are
propagated unchanged by `coerce`. -/
class HHLExtra (M : Type _ → Type _) [Monad M] [HHL M] where
  /-- The value carried by an element, if it is active. -/
  getVal {α : Type _} : elemType M α → Option α
  /-- Propagates an inactive element to another result type. -/
  coerce {α β : Type _} (p : elemType M α) : getVal p = none → elemType M β
  /-- Running a `pure` computation from an active element with value `a` yields an
  active element with value `f a`. -/
  getVal_pure {α β : Type _} (f : α → β) (p : elemType M α) (a : α) (hp : getVal p = some a)
    (q : elemType M β) : relWith (fun v => (pure (f v) : M β)) p q → getVal q = some (f a)
  /-- Propagating an inactive element yields an inactive element. -/
  getVal_coerce {α β : Type _} (p : elemType M α) (h : getVal p = none) :
    getVal (coerce (β := β) p h) = none
  /-- Propagating twice is propagating once. -/
  coerce_coerce {α β γ : Type _} (p : elemType M α) (h : getVal p = none) :
    coerce (β := γ) (coerce (β := β) p h) (getVal_coerce p h) = coerce p h

open HHLExtra

/-! ## The `HHL (NonDetT m)` instance -/

section Instance

/-- Continue from element `p₁`: if it is active with value `b`, continue with `K b`;
if it is inactive, the final element `p'` is `p₁` propagated. -/
def HHLExtra.onVal {m : Type _ → Type _} [Monad m] [HHL m] [HHLExtra m] {δ β : Type _}
    (p₁ : elemType m δ) (K : δ → Prop) (p' : elemType m β) : Prop :=
  match h : getVal p₁ with
  | some b => K b
  | none => p' = coerce p₁ h

/-- `relTree t p p'`: some execution of the computation `t`, started from element
`p`, ends in element `p'`. Choices (`pickCont`) are resolved per execution, and
only the branches actually reached (`vis`) are followed. -/
def NonDetT.relTree {m : Type _ → Type _} [Monad m] [HHL m] [HHLExtra m] {β : Type _} :
    NonDetT m β → {γ : Type _} → elemType m γ → elemType m β → Prop
  | .pure b, _, p, p' => relWith (fun _ => (Pure.pure b : m β)) p p'
  | .vis x f, _, p, p' =>
    ∃ p₁, relWith (fun _ => x) p p₁ ∧ onVal p₁ (fun b => relTree (f b) p₁ p') p'
  | .pickCont _ P f, _, p, p' => ∃ t, P t ∧ relTree (f t) p p'

/-- The `relWith` of `NonDetT m`: run `C` on the value of `p`, or propagate `p`
if it is inactive. -/
def NonDetT.rel {m : Type _ → Type _} [Monad m] [HHL m] [HHLExtra m] {α β : Type _}
    (C : α → NonDetT m β) (p : elemType m α) (p' : elemType m β) : Prop :=
  onVal p (fun v => relTree (C v) p p') p'

lemma HHLExtra.onVal_some {m : Type _ → Type _} [Monad m] [HHL m] [HHLExtra m] {δ β : Type _}
    {p₁ : elemType m δ} {b : δ} (hv : getVal p₁ = some b) (K : δ → Prop) (p' : elemType m β) :
    onVal p₁ K p' ↔ K b := by
  unfold onVal; split <;> simp_all

lemma HHLExtra.onVal_none {m : Type _ → Type _} [Monad m] [HHL m] [HHLExtra m] {δ β : Type _}
    {p₁ : elemType m δ} (hv : getVal p₁ = none) (K : δ → Prop) (p' : elemType m β) :
    onVal p₁ K p' ↔ p' = coerce p₁ hv := by
  unfold onVal; split <;> simp_all

lemma NonDetT.rel_coerce {m : Type _ → Type _} [Monad m] [HHL m] [HHLExtra m] {α₁ α₂ γ : Type _}
    (C : α₁ → NonDetT m α₂) (p : elemType m γ) (h : getVal p = none) (p₂ : elemType m α₂) :
    rel C (coerce p h) p₂ ↔ p₂ = coerce p h := by
  unfold rel
  rw [onVal_none (getVal_coerce p h), coerce_coerce]

/-- One `onVal` step commutes with sequencing. -/
lemma NonDetT.onVal_bind {m : Type _ → Type _} [Monad m] [HHL m] [HHLExtra m] {δ α₁ α₂ : Type _}
    (p₁ : elemType m δ) (K : δ → elemType m α₁ → Prop) (K₂ : δ → Prop)
    (C₂ : α₁ → NonDetT m α₂) (p₂ : elemType m α₂)
    (hK : ∀ b, getVal p₁ = some b → (K₂ b ↔ ∃ q, K b q ∧ rel C₂ q p₂)) :
    (∃ q, onVal p₁ (fun b => K b q) q ∧ rel C₂ q p₂) ↔ onVal p₁ K₂ p₂ := by
  cases hv : getVal p₁ with
  | some b => simp only [onVal_some hv, hK b hv]
  | none =>
    simp only [onVal_none hv]
    constructor
    · rintro ⟨q, rfl, hr⟩; exact (rel_coerce C₂ p₁ hv _).mp hr
    · rintro rfl; exact ⟨coerce p₁ hv, rfl, (rel_coerce C₂ p₁ hv _).mpr rfl⟩

/-- Starting from `p` is the same as first running `pure b` from `p`. -/
lemma NonDetT.relTree_pure_shift {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HHL m]
    [HHLExtra m] {β δ : Type _} (t : NonDetT m β) (b : δ) {γ : Type _} (p : elemType m γ)
    (p' : elemType m β) :
    relTree t p p' ↔ ∃ q, relWith (fun _ : γ => (Pure.pure b : m δ)) p q ∧ relTree t q p' := by
  induction t generalizing γ with
  | pure c =>
    have h := HHL.bind_rel (fun _ : γ => (Pure.pure b : m δ))
      (fun _ : δ => (Pure.pure c : m _)) p p'
    simp only [pure_bind] at h
    simpa [relTree] using h
  | vis x f _ =>
    have h := fun p₁ => HHL.bind_rel (fun _ : γ => (Pure.pure b : m δ)) (fun _ : δ => x) p p₁
    simp only [pure_bind] at h
    simp only [relTree, h]
    grind
  | pickCont τ P f ih =>
    simp only [relTree, ih _ p]
    grind

/-- Sequencing for a single computation tree, run from an active element. -/
lemma NonDetT.relTree_bind {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HHL m] [HHLExtra m]
    {α₁ α₂ : Type _} (t : NonDetT m α₁) (C₂ : α₁ → NonDetT m α₂) {γ : Type _} (p : elemType m γ)
    (hp : ∃ a, getVal p = some a) (p₂ : elemType m α₂) :
    relTree (t.bind C₂) p p₂ ↔ ∃ q, relTree t p q ∧ rel C₂ q p₂ := by
  induction t generalizing γ with
  | pure b =>
    obtain ⟨a, ha⟩ := hp
    simp only [NonDetT.bind, relTree]
    rw [relTree_pure_shift (C₂ b) b p p₂]
    apply exists_congr; intro q
    constructor
    · rintro ⟨hq, hr⟩
      exact ⟨hq, (onVal_some (b := b) (getVal_pure (fun _ => b) p a ha q hq) _ p₂).mpr hr⟩
    · rintro ⟨hq, hr⟩
      exact ⟨hq, (onVal_some (b := b) (getVal_pure (fun _ => b) p a ha q hq) _ p₂).mp hr⟩
  | vis x f ih =>
    simp only [NonDetT.bind, relTree]
    have hK := fun p₁ => onVal_bind p₁ (fun b q => relTree (f b) p₁ q)
      (fun b => relTree ((f b).bind C₂) p₁ p₂) C₂ p₂ (fun b hb => ih b p₁ ⟨b, hb⟩)
    grind
  | pickCont τ P f ih =>
    simp only [NonDetT.bind, relTree, ih _ p hp]
    grind

/-- `NonDetT m` is an `HHL` monad: elements are those of `m`, and `relWith` is
`NonDetT.rel`. -/
instance {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HHL m] [HHLExtra m] :
    HHL (NonDetT m) where
  elemType α := elemType m α
  relWith := NonDetT.rel
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    change NonDetT.rel (fun v => (C₁ v).bind C₂) p₀ p₂ ↔
      ∃ p₁, NonDetT.rel C₁ p₀ p₁ ∧ NonDetT.rel C₂ p₁ p₂
    unfold NonDetT.rel
    exact (NonDetT.onVal_bind p₀ (fun v q => NonDetT.relTree (C₁ v) p₀ q) _ C₂ p₂
      (fun v hv => NonDetT.relTree_bind (C₁ v) C₂ p₀ ⟨v, hv⟩ p₂)).symm

end Instance




/-! ## `NonDetT Id` behaves like `Set` -/

section SetView

/-- Over `Id`, every element is active. -/
instance : HHLExtra Id where
  getVal := some
  coerce _ h := nomatch h
  getVal_pure _ _ _ hp _ h := by cases hp; exact congrArg some h
  getVal_coerce _ h := nomatch h
  coerce_coerce _ h := nomatch h

/-- Set semantics of `NonDetT Id`: all possible results. -/
def NonDetT.sem {α : Type _} : NonDetT Id α → Set α
  | .pure a => {a}
  | .vis x f => sem (f x)
  | .pickCont _ P f => {a | ∃ t, P t ∧ a ∈ sem (f t)}

lemma NonDetT.relTree_Id {β γ : Type _} (t : NonDetT Id β) (p : γ) (p' : β) :
    relTree t p p' ↔ p' ∈ sem t := by
  induction t generalizing γ <;> simp_all [relTree, sem, relWith, onVal]; rfl

/-- A `NonDetT Id` triple holds iff the `Set` triple holds for the set semantics of the program. -/
theorem NonDetT.triple_iff_sem {α β : Type _} (P : Set α → Prop) (C : α → NonDetT Id β)
    (Q : Set β → Prop) :
    triple (M := NonDetT Id) P C Q ↔ triple (M := Set) P (fun a => sem (C a)) Q := by
  have h S : semify (M := NonDetT Id) C S = semify (M := Set) (fun a => sem (C a)) S := by
    ext p'; exact exists_congr fun p => and_congr_right fun _ => relTree_Id (C p) p p'
  simp only [triple, h]; rfl

end SetView
