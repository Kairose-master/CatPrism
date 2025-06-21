/-
Copyright (c) 2025 CatPrism. Released under MIT license.
Author: 진우
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic           -- `simp`, `aesop`, `have`, …

/-!
# CatPrism ‑ Core Library

`CatPrism.Core` 모듈은 프로젝트 전반에서 재사용되는 **기본 카테고리·메트릭·속성 타입클래스**를 정의한다.

* `CatPrismCategory` : `Category`를 래핑하여 CatPrism 전용 네임스페이스를 부여.
* `HasPhase`, `HasLength` : 사상을 실수값 **위상(phase)** 또는 **길이(length)** 로 주석 달기.
* `PhaseDist`, `LengthDist`, `Δzero` : 사상 간 변형(왜곡) 거리.
* `UnitCat` : 단일 객체·단일 사상의 최소 예제 카테고리.

> **참고:**  
> 본 파일은 다른 Core 하위 모듈(`RawPrefunctor`, `EpsFunctor`, `Tactics`)의 **기초**가 되므로  
> **반드시** 이들을 *import* 하지 말아야 순환 의존을 피할 수 있다.
-/

open CategoryTheory
universe u

namespace CatPrism.Core

/-- CatPrism 전용 카테고리 래퍼. 추가 메타데이터를 붙이기 위한 thin‑wrapper 이다. -/
class CatPrismCategory (C : Type u) extends Category C

/-! ## 사상에 부여되는 정량 속성 -/

/-- **위상(phase)** 가 주어지는 사상. 값은 `[-π, π]` 구간으로 제한한다. -/
class HasPhase {C : Type u} [CatPrismCategory C] : Type (u+1) where
  phase     : {A B : C} → (A ⟶ B) → ℝ
  phase_arg : ∀ {A B : C} (f : A ⟶ B), ‖phase f‖ ≤ Real.pi

/-- 두 사상의 위상 차이를 절댓값으로 잰 거리. -/
@[inline]
def PhaseDist {C : Type u} [CatPrismCategory C] [HasPhase (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  ‖HasPhase.phase f - HasPhase.phase g‖

/-- **길이(length)** 가 주어지는 사상. 값은 항상 0 이상. -/
class HasLength {C : Type u} [CatPrismCategory C] : Type (u+1) where
  length     : {A B : C} → (A ⟶ B) → ℝ
  len_nonneg : ∀ {A B : C} (f : A ⟶ B), 0 ≤ length f

/-- 두 사상의 길이 차이를 절댓값으로 잰 거리. -/
@[inline]
def LengthDist {C : Type u} [CatPrismCategory C] [HasLength (C := C)]
    {A B : C} (f g : A ⟶ B) : ℝ :=
  ‖HasLength.length f - HasLength.length g‖

/-- 항상 0을 반환하는 **엄밀(ε = 0) 펑터 검사용** 거리. -/
@[inline] def Δzero {C : Type u} [CatPrismCategory C] {A B : C}
    (_f g : A ⟶ B) : ℝ := 0

/-! ## 최소 예제 카테고리 `UnitCat` -/

/--
`UnitCat`은 단 하나의 객체(`star`)와 단 하나의 사상(`𝟙`)만 갖는
전형적인 **단위(category with one object)** 이다.
-/
inductive UnitCat : Type
| star
deriving DecidableEq, Inhabited

open UnitCat

/-- `UnitCat`에 대한 카테고리(및 CatPrismCategory) 인스턴스. -/
instance : CatPrismCategory UnitCat where
  Hom      := fun _ _ => PUnit           -- 모든 Hom-set은 단일 원소
  id       := fun _ => PUnit.unit
  comp     := fun _ _ _ _ _ => PUnit.unit
  id_comp  := by intros _ _ f; cases f; rfl
  comp_id  := by intros _ _ f; cases f; rfl
  assoc    := by intros _ _ _ _ f g h; cases f; cases g; cases h; rfl

/-- `UnitCat` 모든 사상의 위상은 0. -/
instance : HasPhase (C := UnitCat) where
  phase := by
    intro _ _ _
    exact 0
  phase_arg := by
    intro _ _ _
    have : (0 : ℝ) = 0 := rfl
    have h : ‖(0 : ℝ)‖ ≤ Real.pi := by
      simp [Real.pi_pos.le]
    simpa using h

/-- `UnitCat` 모든 사상의 길이도 0. -/
instance : HasLength (C := UnitCat) where
  length := by
    intro _ _ _
    exact 0
  len_nonneg := by
    intro _ _ _
    simp

end CatPrism.Core
