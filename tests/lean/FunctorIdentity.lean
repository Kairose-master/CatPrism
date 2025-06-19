import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Core.RawPrefunctor
import Core.Tactics
open CategoryTheory
open Core.EpsFunctor
import CatPrism

def IdTest : EpsFunctor (d := fun _ _ _ => (0 : ℝ)) 0 := by
  refine ⟨(fun x => x), (fun f => f), ?_, ?_⟩
  · intro A B C f g; simp
  · intro A; simp

#eval 1
