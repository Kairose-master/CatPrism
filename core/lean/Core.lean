import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic
import Core.RawPrefunctor
import Core.EpsFunctor
import Core.Tactics

open CategoryTheory

universe u

class CatPrismCategory (C : Type u) extends Category C

class HasPhase {C} [CatPrismCategory C] where
  phase     : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : ∀ {A B : C} (f : A ⟶ B), |phase f| ≤ Real.pi

def PhaseDist {C} [CatPrismCategory C] [HasPhase (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasPhase.phase f - HasPhase.phase g|

class HasLength {C} [CatPrismCategory C] where
  length     : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : ∀ {A B : C} (f : A ⟶ B), 0 ≤ length f

def LengthDist {C} [CatPrismCategory C] [HasLength (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasLength.length f - HasLength.length g|

def Δzero {C} [CatPrismCategory C] {A B : C} (_f g : A ⟶ B) : ℝ := 0

/-! ### Example category: `UnitCat` -/

inductive UnitCat
| star

instance : CatPrismCategory UnitCat where
  Hom  := fun _ _ ↦ PUnit
  id   := fun _ ↦ PUnit.unit
  comp := @fun _ _ _ _ _ ↦ PUnit.unit

instance : HasPhase (C := UnitCat) where
  phase     := fun {_ _} _ ↦ 0
  phase_arg := by
    intro; simp [Real.pi_pos.le]
