import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open CategoryTheory
universe u v

class CatPrismCategory (C : Type u) extends Quiver.{v} C, Category.{v} C
namespace CatPrism.Core

@[class] structure HasPhase (C : Type u) [CatPrismCategory C] :
    Type (max u (v+1)) where
  phase     : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : {A B : C} → (f : A ⟶ B) → ‖phase f‖ ≤ Real.pi

@[inline] def PhaseDist
    {C : Type u} [CatPrismCategory C] [h : HasPhase C]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  ‖h.phase f - h.phase g‖

@[class] structure HasLength (C : Type u) [CatPrismCategory C] :
    Type (max u (v+1)) where
  length     : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : {A B : C} → (f : A ⟶ B) → 0 ≤ length f

@[inline] def LengthDist
    {C : Type u} [CatPrismCategory C] [h : HasLength C]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  ‖h.length f - h.length g‖

@[inline] def Δzero
    {C : Type u} [CatPrismCategory C]
    {A B : C} (_f _g : A ⟶ B) : ℝ := 0

inductive UnitCat : Type
| star
deriving DecidableEq, Inhabited

open UnitCat

instance : CatPrismCategory UnitCat where
  Hom      := fun _ _ => PUnit
  id       := fun _ => PUnit.unit
  comp     := fun _ _ _ _ _ => PUnit.unit
  id_comp  := by intro _ _ f; cases f; rfl
  comp_id  := by intro _ _ f; cases f; rfl
  assoc    := by intro _ _ _ _ f g h; cases f; cases g; cases h; rfl

instance : HasPhase UnitCat where
  phase     := fun {_ _} _ => 0
  phase_arg := fun {_ _} _ => by simp [Real.pi_pos.le]

instance : HasLength UnitCat where
  length     := fun {_ _} _ => 0
  len_nonneg := fun {_ _} _ => by simp

end CatPrism.Core