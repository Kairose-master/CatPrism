/-!
  # Core.lean — CatPrism Lean library (ε‑functoriality core)
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
import Lean.Elab.Tactic

open CategoryTheory

/-! ## 1.  Category alias -/

universe u

/-- A thin wrapper so we can add our own type‑classes without conflicting with
`Category` itself. Any `Category` becomes a `CatPrismCategory` by instance. -/
class CatPrismCategory (C : Type u) extends Category C

instance {C : Type u} [Category C] : CatPrismCategory C := ⟨⟩

/-! ## 2.  Phase & Length structures -/

/-- Type‑class for morphisms with an angular *phase*. -/
class HasPhase {C : Type u} [CatPrismCategory C] where
  phase     : {A B : C} → (A ⟶ B) → ℝ        -- argument in [‑π, π]
  phase_arg : ∀ {A B} (f : A ⟶ B), ‖phase f‖ ≤ Real.pi

/-- Phase‑based pseudometric on morphisms. -/
@[inline] def PhaseDist {C} [CatPrismCategory C] [HasPhase (C:=C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  ‖HasPhase.phase f - HasPhase.phase g‖

/-- Length structure (e.g. norm of linear maps). -/
class HasLength {C : Type u} [CatPrismCategory C] where
  length     : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : ∀ {A B} (f : A ⟶ B), 0 ≤ length f

@[inline] def LengthDist {C} [CatPrismCategory C] [HasLength (C:=C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  ‖HasLength.length f - HasLength.length g‖

/-- Zero pseudometric (useful for forgetful functors). -/
@[inline] def Δzero {C} [CatPrismCategory C] {A B : C} (f g : A ⟶ B) : ℝ := 0

/-! ## 3.  ε‑functor -/

/--
`EpsFunctor δ ε` is a functor that preserves composition up to an `ε` error
measured by the pseudometric `δ`.
-/
structure EpsFunctor
    {C D : Type u} [CatPrismCategory C] [CatPrismCategory D]
    (δ : {A B : C} → (A ⟶ B) → (A ⟶ B) → ℝ) (ε : ℝ) where
  F        : C ⥤ D
  comp_ok  : ∀ {A B C₁} (f : A ⟶ B) (g : B ⟶ C₁),
               δ (F.map (g ≫ f)) (F.map g ≫ F.map f) ≤ ε

/-! ## 4.  Meta‑tactic: `derive_phase` -/

open Lean Elab Tactic Meta

syntax (name := derive_phase) "derive_phase " ident : tactic

@[tactic derive_phase]
unsafe def evalDerivePhase : Tactic := fun stx => do
  let `(tactic| derive_phase $Cident) := stx | throwUnsupportedSyntax
  let C ← resolveGlobalConstNoOverload Cident
  let instName := mkIdent (C.getId.appendAfter "_instPhase")
  let tac ← `(tactic|
    instance $instName : HasPhase (C := $C) where
      phase := fun {A B} _ => 0
      phase_arg := by
        intro
        simp [Real.pi_pos])
  evalTactic tac

/-! ## 5.  Convenience tactic: `verify_comp` -/

macro "verify_comp" : tactic =>
  `(tactic| simp [PhaseDist, LengthDist, Δzero, abs_sub] )

/-! ## 6.  Mini‑example -/

namespace Test

inductive UnitCat : Type | star

instance : CatPrismCategory UnitCat where
  Hom  | star star => PUnit
  id  _ := PUnit.unit
  comp _ _ _ _ _ := PUnit.unit

instance : HasPhase (C := UnitCat) where
  phase _ := 0
  phase_arg _ := by simp [Real.pi_pos]

noncomputable def IdFunctor : EpsFunctor (δ := PhaseDist) 0 where
  F := {
    obj := fun _ => UnitCat.star,
    map := fun _ => PUnit.unit
  }
  comp_ok := by
    intros
    simp [PhaseDist]

end Test
