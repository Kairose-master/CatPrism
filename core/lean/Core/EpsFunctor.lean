import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

open CategoryTheory

universe u

/--
`EpsFunctor d ε` is an *ε‑approximate functor* between categories `C` and `D`.  Instead of
requiring exact functoriality, it allows the image of identities and compositions to deviate by at
most `ε` with respect to a user‑supplied *distortion metric* `d` on morphisms of `D`.
- `d f g` measures the distance between two morphisms `f` and `g` in `D`.
- `ε : ℝ` is the tolerated bound (`ε ≥ 0` is assumed by the user).

Only the ordinary categorical structures from `Mathlib` are required, so this file does **not**
import the domain‑specific `CatPrism*` modules.  Project files can provide the relevant instances
when instantiating an `EpsFunctor`.
-/
structure EpsFunctor
    {C D : Type u} [Category C] [Category D]
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    (ε : ℝ) where
  /-- Object mapping. -/
  objMap : C → D
  /-- Morphism mapping. -/
  map    : {A B : C} → (A ⟶ B) → (objMap A ⟶ objMap B)
  /-- Composition is preserved up to `ε`. -/
  comp_ok :
    ∀ {A B C₁ : C} (f : A ⟶ B) (g : B ⟶ C₁),
      d (map (f ≫ g)) ((map f) ≫ (map g)) ≤ ε
  /-- Identities are preserved up to `ε`. -/
  id_ok   : ∀ {A : C}, d (map (𝟙 A)) (𝟙 (objMap A)) ≤ ε

attribute [simp] EpsFunctor.objMap EpsFunctor.map

namespace EpsFunctor

variable {C D : Type u} [Category C] [Category D]

/-- Strict functor ⟶ 0-ε functor, given the distortion metric `d` is reflexive. -/
@[simp] def fromStrict
    (F : C ⥤ D) (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    (hd : ∀ {A B} (f : A ⟶ B), d f f = 0) :
    @EpsFunctor C D _ _ d 0 where
  objMap := F.obj
  map := fun f => F.map f
  comp_ok := by intro _ _ _ f g; rw [F.map_comp]; simp [hd]
  id_ok := by intro A; rw [F.map_id]; simp [hd]

end EpsFunctor
