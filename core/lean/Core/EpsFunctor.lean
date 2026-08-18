import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Core.RawPrefunctor -- ✍️ RawPrefunctor를 임포트합니다. (경로는 실제 프로젝트에 맞게 조정하세요)

open CategoryTheory

universe u

/--
`EpsFunctor d ε` is an *ε‑approximate functor* between categories `C` and `D`.
It builds upon a `RawPrefunctor` by adding laws that require identity and
composition to be preserved up to a tolerance `ε` with respect to a user-supplied
*distortion metric* `d` on morphisms of `D`.
-/
structure EpsFunctor
    {C D : Type u} [Category C] [Category D]
    (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    (ε : ℝ) where
  /-- ✍️ The underlying mapping of objects and morphisms (the data). -/
  F : RawPrefunctor C D
  /-- Composition is preserved up to `ε`. -/
  comp_ok :
    ∀ {A B C₁ : C} (f : A ⟶ B) (g : B ⟶ C₁),
      d (F.map (f ≫ g)) (F.map f ≫ F.map g) ≤ ε
  /-- Identities are preserved up to `ε`. -/
  id_ok   : ∀ {A : C}, d (F.map (𝟙 A)) (𝟙 (F.obj A)) ≤ ε

-- ✍️ EpsFunctor의 RawPrefunctor 필드에 simp 속성을 부여합니다.
attribute [simp] EpsFunctor.F

namespace EpsFunctor

variable {C D : Type u} [Category C] [Category D]

/-- Strict functor ⟶ 0-ε functor, given the distortion metric `d` is reflexive. -/
@[simp] def fromStrict
    (F_strict : C ⥤ D) (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    (hd : ∀ {A B} (f : A ⟶ B), d f f = 0) :
    @EpsFunctor C D _ _ d 0 := by
  let F_raw : RawPrefunctor C D := { obj := F_strict.obj, map := F_strict.map }
  refine { F := F_raw, comp_ok := ?_, id_ok := ?_ }
  · intro A B C₁ f g
    show d (F_strict.map (f ≫ g)) (F_strict.map f ≫ F_strict.map g) ≤ 0
    rw [F_strict.map_comp]; simp [hd]
  · intro A
    show d (F_strict.map (𝟙 A)) (𝟙 (F_strict.obj A)) ≤ 0
    rw [F_strict.map_id]; simp [hd]

end EpsFunctor
