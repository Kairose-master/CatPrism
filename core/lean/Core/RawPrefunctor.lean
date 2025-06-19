import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

universe u

/-- Raw object & morphism mapping, no laws. -/
structure RawPrefunctor {C D : Type u} [Category C] [Category D] where
  objMap : C → D
  morMap : {A B : C} → (A ⟶ B) → (objMap A ⟶ objMap B)
