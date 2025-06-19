/-!
# CatPrism Core Library

This file defines the foundational typeclasses and structures for the CatPrism project.
It establishes ththroughout the system, from the DSL parser to the Lean proof engine.

## Main Components:
- `CatPrismCategory`: A simple extension of `Mathlib`'s `Category` for namespacing.
- `HasPhase`, `HasLength`: Typeclasses to equip morphisms with quantitative attributes.
- `PhaseDist`, `LengthDist`: Distortion metrics derived from the attributes above.
- `Δzero`: A trivial metric for exact functoriality checks.
- `UnitCat`: A minimal example category for testing and demonstration.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

-- It is assumed these files are in the `Core` directory, sibling to this file.
import Core.RawPrefunctor
import Core.EpsFunctor
import Core.Tactics

open CategoryTheory

universe u

namespace CatPrism.Core

/--
A typeclass for categories relevant to the CatPrism project.
This serves as a wrapper around `Mathlib.CategoryTheory.Category` to allow for
project-specific instance management and organization.
-/
class CatPrismCategory (C : Type u) extends Category C

/--
A typeclass for morphisms that have a notion of "phase".
The phase is represented as a real number, typically bounded within `[-π, π]`,
analogous to the argument of a complex number.
-/
class HasPhase {C} [CatPrismCategory C] where
  /-- The phase of a morphism, as a real number. -/
  phase     : {A B : C} → (A ⟶ B) → ℝ
  /-- The phase value is bounded by `±π`. -/
  phase_arg : ∀ {A B : C} (f : A ⟶ B), |phase f| ≤ Real.pi

/--
A distortion metric that measures the absolute difference between the phases of two morphisms.
This is a key metric for analyzing rotational or cyclical transformations.
-/
def PhaseDist {C} [CatPrismCategory C] [HasPhase (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasPhase.phase f - HasPhase.phase g|

/--
A typeclass for morphisms that have a notion of "length" or "magnitude".
The length is a non-negative real number.
-/
class HasLength {C} [CatPrismCategory C] where
  /-- The length of a morphism. -/
  length     : {A B : C} → (A ⟶ B) → ℝ
  /-- The length must be non-negative. -/
  len_nonneg : ∀ {A B : C} (f : A ⟶ B), 0 ≤ length f

/--
A distortion metric that measures the absolute difference between the lengths of two morphisms.
This is useful for analyzing transformations involving scaling or magnitude changes.
-/
def LengthDist {C} [CatPrismCategory C] [HasLength (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasLength.length f - HasLength.length g|

/--
A trivial "zero" metric that always returns 0.
This is used to model strict, non-approximate functors within the `EpsFunctor` framework
by setting `ε = 0`.
-/
def Δzero {C} [CatPrismCategory C] {A B : C} (_f g : A ⟶ B) : ℝ := 0


/-! ### Example category: `UnitCat` -/

/--
A minimal category with a single object (`star`) and a single morphism (the identity).
Useful for testing fundamental structures without combinatorial complexity.
-/
inductive UnitCat
| star
deriving Inhabited -- Allows creating a default instance of `UnitCat`.

instance : CatPrismCategory UnitCat where
  Hom  := fun _ _ ↦ PUnit
  id   := fun _   ↦ PUnit.unit
  comp := fun _ _ ↦ PUnit.unit

instance : HasPhase (C := UnitCat) where
  phase     := fun _ _ ↦ 0
  phase_arg := by
    -- The proof is trivial since phase is always 0.
    intro _ _ _
    simp [Real.pi_pos.le]

end CatPrism.Coree basic vocabulary for categories, morphisms, and distortion metrics
that are used 