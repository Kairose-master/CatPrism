import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

universe u

/--
A `RawPrefunctor` is the raw data of a functor: a map on objects and a map on morphisms.
It does not need to preserve identities or composition.

This version includes `mathlib`-conventional naming (`obj`, `map`), `CoeFun` for
ergonomic object mapping (`F A` instead of `F.obj A`), and `@[simp]` attributes
to aid the simplifier tactic in proofs.
-/
@[ext] -- ✍️ `ext` 속성 추가: 두 RawPrefunctor가 모든 객체와 사상에 대해 동일하게 작용하면 동일하다고 추론
structure RawPrefunctor (C D : Type u) [Category C] [Category D] where
  /-- The object mapping. Use `F A` for `F.obj A`. -/
  @[simp]
  obj : C → D
  /-- The morphism mapping. -/
  @[simp]
  map : {A B : C} → (A ⟶ B) → (obj A ⟶ obj B)

/-- Allows a `RawPrefunctor` `F` to be called like a function on objects, e.g., `F A`. -/
instance {C D : Type u} [Category C] [Category D] : CoeFun (RawPrefunctor C D) (fun _ => C → D) where
  coe F := F.obj
