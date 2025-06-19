import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Core.RawPrefunctor
import Mathlib.Tactic
open CategoryTheory
open Lean Elab Tactic

elab "verify_id" : tactic => do
  evalTactic (← `(tactic|
    first
      | simp
      | apply le_of_eq; simp
      | linarith))

macro "verify_comp" : tactic => `(tactic| simp)

