open Core.EpsFunctor
open CategoryTheory

variable {d : {A B : UnitCat} → (A ⟶ B) → (A ⟶ B) → ℝ}
variable (ε : ℝ)

/-- trivial ε-functor on the UnitCat – compiles / test -/
def UnitEps (hε : 0 ≤ ε) : Core.EpsFunctor.EpsFunctor d ε where
  objMap := fun _ ↦ UnitCat.star
  map := by
    intro _ _ _
    exact PUnit.unit
  comp_ok := by
    intro _ _ _ _ _
    simpa using le_of_eq (by simp)
  id_ok := by
    intro _
    simpa using le_of_eq (by simp)
