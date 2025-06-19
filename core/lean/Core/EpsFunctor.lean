import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Core.RawPrefunctor

open CategoryTheory

universe u

/-- ε-functor now checks identities. -/
structure EpsFunctor {C D : Type u} [CatPrismCategory C] [CatPrismCategory D]
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ) (ε : ℝ) where
  obj_map : C → D
  map     : {A B : C} → (A ⟶ B) → (obj_map A ⟶ obj_map B)
  comp_ok :
    ∀ {A B C₁} (f : A ⟶ B) (g : B ⟶ C₁),
      d (map (g ≫ f)) ((map f) ≫ (map g)) ≤ ε
  id_ok   :
    ∀ {A}, d (map (𝟙 A)) (𝟙 (obj_map A)) ≤ ε

/-- Embed a strict functor as 0-ε ε-functor. -/
@[simp]
def EpsFunctor.fromStrict {C D : Type u} [CatPrismCategory C] [CatPrismCategory D]
    (F : C ⥤ D)
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    [h : ∀ {A B} (f : A ⟶ B), Decidable (d f f = 0)] :
    EpsFunctor d 0 := by
  classical
  refine {
    obj_map := F.obj,
    map := ?_,
    comp_ok := ?_,
    id_ok := ?_ }
  · intro A B f; exact F.map f
  · intro A B C₁ f g
    have := F.map_comp f g
    simp [this, h]
  · intro A
    have := F.map_id A
    simp [this, h]
