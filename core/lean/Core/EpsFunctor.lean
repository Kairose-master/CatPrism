import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic

open CategoryTheory

/-!
  # `EpsFunctor` — ε‑approximate functors

  *   **Goal** : capture functors that preserve identities and composition *up to a real error ε*,
      measured by a user‑supplied distortion pseudo‑metric `d` on morphisms of the *target* category.
  *   **Notation** : `d f g` is the distance between two morphisms `f`,`g : A ⟶ B` in `D`.
  *   **Laws**   :

        `d (F.map (g ≫ f)) ((F.map f) ≫ (F.map g)) ≤ ε`
        `d (F.map (𝟙 A)) (𝟙 (F.obj A))               ≤ ε`

      When `ε = 0` and `d` is a genuine metric, we recover ordinary functors.
-!/

universe u

/--
An **ε‑functor** between categories `C` and `D`.  The parameter `d` measures how far two
morphisms of `D` are, while `ε` bounds the functorial error.  When `ε = 0`, every `EpsFunctor d 0`
is strictly functorial.
-/
structure EpsFunctor
    {C D : Type u} [Category C] [Category D]
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    (ε : ℝ) : Type u where
  /-- Object part of the ε‑functor. -/
  objMap : C → D
  /-- Morphism part. -/
  map    : {A B : C} → (A ⟶ B) → (objMap A ⟶ objMap B)
  /-- Composition is preserved up to ε. -/
  comp_ok :
    ∀ {A B C'} (f : A ⟶ B) (g : B ⟶ C'),
      d (map (g ≫ f)) ((map f) ≫ (map g)) ≤ ε
  /-- Identities are preserved up to ε. -/
  id_ok :
    ∀ {A}, d (map (𝟙 A)) (𝟙 (objMap A)) ≤ ε

namespace EpsFunctor

/-- Promote an ordinary functor to a *perfect* (`ε = 0`) ε‑functor. -/
def fromStrict
    {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D)
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    [∀ {A B} (f : A ⟶ B), Decidable (d f f = 0)] :
    EpsFunctor d 0 :=
  { objMap := F.obj,
    map    := F.map,
    comp_ok := by
      intro A B C' f g
      simp [F.map_comp],
    id_ok := by
      intro A
      simp [F.map_id] }

end EpsFunctor