import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic

open CategoryTheory

universe u

/-- A thin wrapper around `Category` so we can add extra structure later. -/
class CatPrismCategory (C : Type u) extends Category C

/-- Morphisms endowed with a phase (angle in ℝ). -/
class HasPhase {C} [CatPrismCategory C] where
  phase     : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : ∀ {A B : C} (f : A ⟶ B), |phase f| ≤ Real.pi

def PhaseDist {C} [CatPrismCategory C] [HasPhase (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasPhase.phase f - HasPhase.phase g|

/-- Optional length structure (useful for vector-like morphisms). -/
class HasLength {C} [CatPrismCategory C] where
  length     : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : ∀ {A B : C} (f : A ⟶ B), 0 ≤ length f

def LengthDist {C} [CatPrismCategory C] [HasLength (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasLength.length f - HasLength.length g|

/-- Trivial pseudometric that is constantly 0 (for forgetful functors). -/
def Δzero {C} [CatPrismCategory C] {A B : C} (_f g : A ⟶ B) : ℝ := 0

/--  
An **ε-functor**: a functor that preserves composition _within ε_  
under a user-supplied pseudometric `δ`.
-/
structure EpsFunctor
    {C D : Type u} [CatPrismCategory C] [CatPrismCategory D]
    (δ : {A B : C} → (A ⟶ B) → (A ⟶ B) → ℝ) (ε : ℝ) where
  F : C ⥤ D
  comp_ok :
    ∀ {A B C₁ : C} (f : A ⟶ B) (g : B ⟶ C₁),
      δ (F.map (g ≫ f)) ((F.map g) ≫ (F.map f)) ≤ ε

/-! ## Minimal working example: `UnitCat` -/

inductive UnitCat
| star

instance : CatPrismCategory UnitCat where
  Hom  := fun _ _ ↦ PUnit
  id   := fun _ ↦ PUnit.unit
  comp := fun _ _ _ _ _ ↦ PUnit.unit

instance : HasPhase (C := UnitCat) where
  phase      := fun {_ _} _ ↦ 0
  phase_arg  := by
    intro; simp [Real.pi_pos.le]

/-- Identity functor on `UnitCat`, trivially 0-distortion. -/
def IdFunctor : EpsFunctor (δ := PhaseDist) 0 where
  F := { obj := id, map := fun _ ↦ PUnit.unit }
  comp_ok := by
    intro A B C₁ f g
    simp [PhaseDist]