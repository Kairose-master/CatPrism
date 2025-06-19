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
    (ε : ℝ) : Type (u+1) where
  /-- ✍️ The underlying mapping of objects and morphisms (the data). -/
  F : RawPrefunctor C D
  /-- Composition is preserved up to `ε`. -/
  comp_ok :
    ∀ {A B C₁ : C} (f : A ⟶ B) (g : B ⟶ C₁),
      -- ✍️ 중요: 펑터의 올바른 합성 순서로 수정되었습니다.
      d (F.map (g ≫ f)) (F.map g ≫ F.map f) ≤ ε
  /-- Identities are preserved up to `ε`. -/
  id_ok   : ∀ {A : C}, d (F.map (𝟙 A)) (𝟙 (F.obj A)) ≤ ε

-- ✍️ EpsFunctor의 RawPrefunctor 필드에 simp 속성을 부여합니다.
attribute [simp] EpsFunctor.F

namespace EpsFunctor

variable {C D : Type u} [Category C] [Category D]

/-- Strict functor ⟶ 0-ε functor -/
@[simp] def fromStrict
    (F_strict : C ⥤ D) (d : {A B : D} → (A ⟶ B) → (A ⟶ B) → ℝ)
    [∀ {A B} (f : A ⟶ B), Decidable (d f f = 0)] :
    EpsFunctor d 0 := by
  -- ✍️ 먼저 RawPrefunctor 데이터를 생성합니다.
  let F_raw : RawPrefunctor C D := { obj := F_strict.obj, map := F_strict.map }
  -- ✍️ 새로운 구조에 맞게 EpsFunctor를 생성합니다.
  refine { F := F_raw, comp_ok := ?_, id_ok := ?_ }
  · intro A B C₁ f g; simp [F_strict.map_comp] -- 이제 simp가 완벽하게 작동합니다.
  · intro A; simp [F_D.map_id]

end EpsFunctor
