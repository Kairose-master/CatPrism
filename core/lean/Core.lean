import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic

open CategoryTheory

universe u

/-- Alias to mark any mathlib category as a CatPrism category. -/
class CatPrismCategory (C : Type u) extends Category C

/-- Morphisms equipped with a phase (angle in radians). -/
class HasPhase {C : Type u} [CatPrismCategory C] where
  phase     : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : ∀ {A B} (f : A ⟶ B), |phase f| ≤ Real.pi

/-- Phase‑based pseudometric. -/
def PhaseDist {C : Type u} [CatPrismCategory C] [HasPhase (C:=C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasPhase.phase f - HasPhase.phase g|

/-- Morphisms equipped with a (non‑negative) length. -/
class HasLength {C : Type u} [CatPrismCategory C] where
  length     : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : ∀ {A B} (f : A ⟶ B), 0 ≤ length f

/-- Length‑based pseudometric. -/
def LengthDist {C : Type u} [CatPrismCategory C] [HasLength (C:=C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasLength.length f - HasLength.length g|

/-- Trivial zero pseudometric (useful for forgetful functors). -/
@[simp] def Δzero {C : Type u} [CatPrismCategory C] {A B : C}
    (f g : A ⟶ B) : ℝ := 0

/-- `ε`‑functor: composition is preserved within `ε` under a metric `δ`. -/
structure EpsFunctor
    {C D : Type u} [CatPrismCategory C] [CatPrismCategory D]
    (δ : {A B : C} → (A ⟶ B) → (A ⟶ B) → ℝ) (ε : ℝ) where
  F : C ⥤ D
  comp_ok :
    ∀ {A B C' : C} (f : A ⟶ B) (g : B ⟶ C'),
      δ (F.map (g ≫ f)) ((F.map g) ≫ (F.map f)) ≤ ε

/-! ### Minimal working example -/
namespace Test

inductive UnitCat | star

instance : CatPrismCategory UnitCat where
  Hom _ _   := PUnit
  id _      := PUnit.unit
  comp _ _ _ _ _ := PUnit.unit

instance : HasPhase (C := UnitCat) where
  phase _      := 0
  phase_arg _  := by simp [Real.pi_pos]

instance : HasLength (C := UnitCat) where
  length _     := 0
  len_nonneg _ := by simp

/-- Identity functor seen as an `ε`‑functor with `ε = 0`. -/
def IdFunctor : EpsFunctor (δ := PhaseDist) 0 where
  F := { obj := fun _ => UnitCat.star,
         map := fun _ => PUnit.unit }
  comp_ok := by
    intro; simp [PhaseDist]

end Test