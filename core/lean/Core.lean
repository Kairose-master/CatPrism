import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

open CategoryTheory

universe u

/--
`EpsFunctor d ε` is an *ε‑functor* between categories `C` and `D`.  Instead of preserving
composition and identities strictly, it does so *up to a numerical error* `ε`, measured by the
user‑supplied *distortion metric* `d` on morphisms of `D`.

* `d f g` should be thought of as the "distance" between two parallel morphisms `f` and `g` in
  `D`.  No axioms on `d` are required—any real‑valued function will do—but typical examples are
  metrics coming from a norm or an absolute value.
* When `ε = 0` and `d` is the discrete metric, an `EpsFunctor` is just an ordinary functor.
* If `ε = 0` but `d` is non‑trivial, we obtain *isometric* functors, useful in analysis.
-/
structure EpsFunctor
    {C D : Type u} [Category C] [Category D]
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    (ε : ℝ) : Type (max u (u+1)) where
  /-- Object mapping. -/
  objMap : C → D
  /-- Morphism mapping. -/
  map    : {A B : C} → (A ⟶ B) → (objMap A ⟶ objMap B)
  /-- Composition is preserved *up to* `ε`. -/
  comp_ok : ∀ {A B C₁ : C} (f : A ⟶ B) (g : B ⟶ C₁),
      d (map (g ≫ f)) ((map f) ≫ (map g)) ≤ ε
  /-- Identities are preserved *up to* `ε`. -/
  id_ok   : ∀ {A : C}, d (map (𝟙 A)) (𝟙 (objMap A)) ≤ ε

attribute [simp] EpsFunctor.objMap
attribute [simp] EpsFunctor.map

namespace EpsFunctor

variable {C D : Type u} [Category C] [Category D]
variable {d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ} {ε : ℝ}

/-- A strict functor is automatically a `0`‑ε functor. -/
@[simp]
def fromStrict
    (F : C ⥤ D) (d)
    [∀ {A B : D} (f : A ⟶ B), Decidable (d f f = 0)] :
    EpsFunctor d 0 where
  objMap := F.obj
  map    := @fun A B f => F.map f
  comp_ok := by
    intro A B C₁ f g
    simp [F.map_comp]
  id_ok := by
    intro A
    simp [F.map_id]

end EpsFunctor