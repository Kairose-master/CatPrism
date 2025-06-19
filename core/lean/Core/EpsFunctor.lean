import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Core.RawPrefunctor
import Core.Tactics

open CategoryTheory

universe u

variable {C D : Type u}
variable [CatPrismCategory C] [CatPrismCategory D]

instance instQuiverC : Quiver C := inferInstance
instance instCategoryC : Category C := inferInstance
instance instQuiverD : Quiver D := inferInstance
instance instCategoryD : Category D := inferInstance

/-- ε-functor now checks identities. -/
structure EpsFunctor
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    (ε : ℝ) : Type u where
  @[simp] obj_map : C → D
  @[simp] map     : {A B : C} → (A ⟶ B) → (obj_map A ⟶ obj_map B)
  comp_ok :
    ∀ {A B C₁} (f : A ⟶ B) (g : B ⟶ C₁),
      d (map (g ≫ f)) ((map f) ≫ (map g)) ≤ ε
  id_ok   :
    ∀ {A}, d (map (𝟙 A)) (𝟙 (obj_map A)) ≤ ε

/-- Embed a strict functor as 0-ε ε-functor. -/
@[simp]
def EpsFunctor.fromStrict
    (F : C ⥤ D)
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    [∀ {A B} (f : A ⟶ B), Decidable (d f f = 0)] :
    EpsFunctor (C := C) (D := D) d 0 := by
  classical
  refine {
    obj_map := F.obj,
    map := F.map,
    comp_ok := ?_,
    id_ok := ?_ }
  · intro A B C₁ f g
    simp [F.map_comp]
  · intro A
    simp [F.map_id]
