import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open CategoryTheory
universe u

namespace CatPrism.Core

class CatPrismCategory (C : Type u) extends Category C

class HasPhase {C : Type u} [CatPrismCategory C] : Type (u+2) where
  phase     : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : ∀ {A B : C} (f : A ⟶ B), ‖phase f‖ ≤ Real.pi

@[inline] def PhaseDist {C : Type u} [CatPrismCategory C] [HasPhase (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  ‖HasPhase.phase f - HasPhase.phase g‖

class HasLength {C : Type u} [CatPrismCategory C] : Type (u+2) where
  length     : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : ∀ {A B : C} (f : A ⟶ B), 0 ≤ length f

@[inline] def LengthDist {C : Type u} [CatPrismCategory C] [HasLength (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  ‖HasLength.length f - HasLength.length g‖

@[inline] def Δzero {C : Type u} [CatPrismCategory C] {A B : C}
    (_f _g : A ⟶ B) : ℝ :=
  0

inductive UnitCat : Type
| star
deriving DecidableEq, Inhabited

open UnitCat

instance : CatPrismCategory UnitCat where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp := by
    intro _ _ _ _ _
    exact PUnit.unit
  id_comp := by
    intro _ _ f
    cases f
    simp
  comp_id := by
    intro _ _ f
    cases f
    simp
  assoc := by
    intro _ _ _ _ f g h
    cases f
    cases g
    cases h
    simp

instance : HasPhase (C := UnitCat) where
  phase := by
    intro _ _ _
    exact 0
  phase_arg := by
    intro _ _ _
    simp [Real.pi_pos.le]

instance : HasLength (C := UnitCat) where
  length := by
    intro _ _ _
    exact 0
  len_nonneg := by
    intro _ _ _
    simp

end CatPrism.Core

