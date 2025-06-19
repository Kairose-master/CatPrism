/-!
  Core.lean — CatPrism Lean library (ε‑functoriality core)
  --------------------------------------------------------
  • Category / Functor structures (alias to Mathlib4)
  • Distortion pseudometrics: PhaseDist, LengthDist, Δzero
  • derive_phase meta‑tactic
  • verify_comp default tactic
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Basic
import Lean.Elab.Tactic

open CategoryTheory
open Lean
open Lean.Elab
open Lean.Elab.Tactic

/-- Base alias for categories from mathlib. -/
universe u

class CatPrismCategory (C : Type u) extends Category C

/-- Typeclass for a phase‐bearing hom‑set (`phase f ∈ [-π, π]`). -/
class HasPhase {C : Type u} [CatPrismCategory C] : Type (u+1) where
  phase     : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : ∀ {A B} (f : A ⟶ B), abs (phase f) ≤ Real.pi

/--
  Phase‑based pseudometric on morphisms:

  `δθ(f,g) := |phase f − phase g|`.
-/
def PhaseDist {C : Type u} [CatPrismCategory C] [HasPhase (C:=C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  abs (HasPhase.phase f - HasPhase.phase g)

/-- Length‑based pseudometric (for categories equipped with a length on morphisms). -/
class HasLength {C : Type u} [CatPrismCategory C] : Type (u+1) where
  length     : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : ∀ {A B} (f : A ⟶ B), 0 ≤ length f

def LengthDist {C : Type u} [CatPrismCategory C] [HasLength (C:=C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  abs (HasLength.length f - HasLength.length g)

/-- Zero pseudometric (used e.g. for forgetful functors). -/
def Δzero {C : Type u} [CatPrismCategory C] {A B : C} (_f _g : A ⟶ B) : ℝ := 0

/-- ε‑functor: preserves composition within ε under a metric δ. -/
structure EpsFunctor
    {C D : Type u} [CatPrismCategory C] [CatPrismCategory D]
    (δ : {A B : C} → (A ⟶ B) → (A ⟶ B) → ℝ) (ε : ℝ) : Type (u+1) where
  F        : C ⥤ D
  comp_ok :
    ∀ {A B C₁ : C} (f : A ⟶ B) (g : B ⟶ C₁),
      δ (F.map (f ≫ g)) (F.map f ≫ F.map g) ≤ ε

/-- `derive_phase` meta‑tactic: automatically create a trivial `HasPhase` instance. -/
syntax (name := derive_phase) "derive_phase " ident : tactic

@[tactic derive_phase] def evalDerivePhase : Tactic := fun stx => do
  let `(tactic| derive_phase $Cident) := stx
    | throwUnsupportedSyntax
  let C ← Tactic.resolveGlobalConstNoOverload Cident
  let instName := mkIdent (C.getId ++ `instPhase)
  let tac ← `(tactic|
    instance $instName : HasPhase (C := $C) where
      phase := fun {A B} _f => 0
      phase_arg := by
        intro
        have h : (0 : ℝ) ≤ Real.pi := (Real.pi_pos).le
        simpa using h )
  Tactic.evalTactic tac

/-- `verify_comp` tactic: closes goals of the form `δ _ _ ≤ ε` by `simp`. -/
macro "verify_comp" : tactic =>
  `(tactic| intros; simp [PhaseDist, LengthDist, Δzero, abs_sub])

/-! ## Example: trivial category instance *-/

namespace Test

inductive UnitCat : Type
| star

instance : CatPrismCategory UnitCat where
  Hom := fun _ _ => PUnit
  id  := fun _ => PUnit.unit
  comp := fun _ _ _ _ _ => PUnit.unit

instance : HasPhase (C := UnitCat) where
  phase _ := 0
  phase_arg _ := by
    have h : (0 : ℝ) ≤ Real.pi := (Real.pi_pos).le
    simpa using h

def idFunctor : EpsFunctor (δ := PhaseDist) 0 where
  F := { obj := id, map := fun _ => PUnit.unit }
  comp_ok := by
    intro
    simp [PhaseDist]

end Test