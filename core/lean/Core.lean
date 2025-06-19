import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic

open CategoryTheory

universe u

class CatPrismCategory (C : Type u) extends Category C

class HasPhase {C} [CatPrismCategory C] where
  phase : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : ∀ {A B : C} (f : A ⟶ B), abs (phase f) ≤ Real.pi

def PhaseDist {C} [CatPrismCategory C] [HasPhase (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  abs (HasPhase.phase f - HasPhase.phase g)

class HasLength {C} [CatPrismCategory C] where
  length : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : ∀ {A B : C} (f : A ⟶ B), 0 ≤ length f

def LengthDist {C} [CatPrismCategory C] [HasLength (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  abs (HasLength.length f - HasLength.length g)

def Δzero {C} [CatPrismCategory C] {A B : C} (f g : A ⟶ B) : ℝ := 0

structure EpsFunctor
    {C D : Type u} [CatPrismCategory C] [CatPrismCategory D]
    (δ : {A B : C} → (A ⟶ B) → (A ⟶ B) → ℝ) (ε : ℝ) where
  F : C ⥤ D
  comp_ok :
    ∀ {A B C₁ : C} (f : A ⟶ B) (g : B ⟶ C₁),
      δ (F.map (g ≫ f)) ((F.map g) ≫ (F.map f)) ≤ ε

inductive UnitCat
| star

instance : CatPrismCategory UnitCat where
  Hom := fun _ _ => PUnit
  id := fun _ => PUnit.unit
  comp := @fun _ _ _ _ _ => PUnit.unit

instance : HasPhase (C := UnitCat) where
  phase := fun {A B} _ => 0
  phase_arg := fun {A B} f =>
    abs_le.2 ⟨by simp [Real.pi_pos.le], by simp [Real.pi_pos.le]⟩

def IdFunctor : EpsFunctor (δ := PhaseDist) 0 where
  F := { obj := id, map := fun _ => PUnit.unit }
  comp_ok := by
    intros; simp [PhaseDist]