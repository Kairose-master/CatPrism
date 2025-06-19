import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Core.RawPrefunctor
import Core.Tactics
open CategoryTheory
open Core.EpsFunctor
import CatPrism

/-- EpsFunctor on `UnitCat` using `PhaseDist` as the metric. -/
def UnitPhaseId : EpsFunctor (d := PhaseDist) 0 := by
  refine {
    objMap := fun _ => UnitCat.star,
    map := fun {A B} f => PUnit.unit,
    comp_ok := ?_,
    id_ok := ?_ }
  · intro A B C f g; verify_comp
  · intro A; verify_id

