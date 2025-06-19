import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
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
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ) (ε : ℝ) : Type (max u 1) where
  /-- Object mapping. -/
  objMap : C → D
  /-- Morphism mapping. -/
  map    : {A B : C} → (A ⟶ B) → (objMap A ⟶ objMap B)
  /-- Composition is preserved up to `ε`. -/
  comp_ok :
    ∀ {A B C'} (f : A ⟶ B) (g : B ⟶ C'),
      d (map (f ≫ g)) (map f ≫ map g) ≤ ε
  /-- Identities are preserved up to `ε`. -/
  id_ok   : ∀ {A}, d (map (𝟙 A)) (𝟙 (objMap A)) ≤ ε

attribute [simp] EpsFunctor.objMap EpsFunctor.map

/-- Embed a strict functor as a `0`‑ε functor. -/
@[simp]
def EpsFunctor.fromStrict
    {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D)
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    [∀ {A B} (f : A ⟶ B), Decidable (d f f = 0)] :
    EpsFunctor (C := C) (D := D) d 0 := by
  classical
  exact
    { objMap := F.obj,
      map    := F.map,
      comp_ok := by
        intro A B C' f g
        -- `map` is strict, so the distance is zero.
        change d _ _ ≤ 0
        simp [F.map_comp, le_of_eq] at *,
      id_ok := by
        intro A
        change d _ _ ≤ 0
        simp [F.map_id, le_of_eq] }
