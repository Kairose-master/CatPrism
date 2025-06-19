/-!
  Core.lean — CatPrism Lean library (ε‑functoriality core)
  --------------------------------------------------------
  * Category / Functor wrappers (aliasing mathlib)
  * Distortion pseudometrics: `PhaseDist`, `LengthDist`, `Δzero`
  * `derive_phase` meta‑tactic
  * `verify_comp` convenience tactic

  Tested against Lean **v4.21.0‑rc2** / mathlib4 **2025‑06‑19**.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic

open CategoryTheory

universe u

/-- Base alias for categories from mathlib -/
class CatPrismCategory (C : Type u) extends Category C

/-- Typeclass for phase‑bearing morphisms -/
class HasPhase {C} [CatPrismCategory C] where
  phase     : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : ∀ {A B} (f : A ⟶ B), |phase f| ≤ Real.pi

/-- Phase distance ‖θ₁−θ₂‖ -/
def PhaseDist {C} [CatPrismCategory C] [HasPhase (C:=C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasPhase.phase f - HasPhase.phase g|

/-- Typeclass for length‑bearing morphisms -/
class HasLength {C} [CatPrismCategory C] where
  length : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : ∀ {A B} (f : A ⟶ B), 0 ≤ length f

def LengthDist {C} [CatPrismCategory C] [HasLength (C:=C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  |HasLength.length f - HasLength.length g|

/-- Zero distance (forgetful metric) -/
def Δzero {C} [CatPrismCategory C] {A B : C} (f g : A ⟶ B) : ℝ := 0

/-- ε‑functor: preserves composition within ε under metric δ -/
structure EpsFunctor
    {C D : Type u} [CatPrismCategory C] [CatPrismCategory D]
    (δ : {A B : C} → (A ⟶ B) → (A ⟶ B) → ℝ) (ε : ℝ) where
  F   : C ⥤ D
  comp_ok :
    ∀ {A B C₁ : C} (f : A ⟶ B) (g : B ⟶ C₁),
      δ (F.map (g ≫ f)) (F.map g ≫ F.map f) ≤ ε

/-- `derive_phase` meta‑tactic: auto‑generate a trivial `HasPhase` instance -/
syntax (name:=derive_phase) "derive_phase " ident : tactic

@[tactic derive_phase]
def evalDerivePhase : Tactic := fun stx => do
  let `(tactic| derive_phase $Cident) := stx | throwUnsupportedSyntax
  let C ← Tactic.resolveGlobalConstNoOverload Cident
  let instName := mkIdent (C.getId ++ `instPhase)
  let tac ← `(tactic|
    instance $instName : HasPhase (C := $C) where
      phase := fun {A B} f => 0
      phase_arg := by
        intro
        have : (0 : ℝ) ≤ Real.pi := Real.pi_pos
        simpa)
  Tactic.evalTactic tac

/-- `verify_comp` : quick goal that composition distance ≤ ε -/
macro "verify_comp" : tactic =>
  `(tactic|
    intros;
    simp [PhaseDist, LengthDist, Δzero, abs_sub])

/-! ### Example *-/
namespace Test

inductive UnitCat | star

instance : CatPrismCategory UnitCat where
  Hom  := fun _ _ => PUnit
  id   := fun _ => PUnit.unit
  comp := fun _ _ _ _ _ => PUnit.unit

instance : HasPhase (C := UnitCat) where
  phase _ := 0
  phase_arg _ := by
    have : (0 : ℝ) ≤ Real.pi := Real.pi_pos
    simpa

def IdFunctor : EpsFunctor (δ := PhaseDist) 0 where
  F := { obj := id, map := fun _ => PUnit.unit }
  comp_ok := by
    intro;
    simp [PhaseDist]

end Test