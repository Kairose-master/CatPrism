import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic               -- `simp`, `norm_num`, …
import Mathlib.Tactic.Linarith      -- `linarith`
import Core.RawPrefunctor           -- (앞으로의 전술에서 사용할 수 있도록 미리 로드)

open CategoryTheory
open Lean
open Lean.Elab
open Lean.Elab.Tactic

/-!
# CatPrism ‑ 전용 전술 모음

`verify_id`, `verify_comp` 두 가지 자동화 전술을 제공한다.

* `verify_id`  : 항등 사상 보존 목표 `d (F.map (𝟙 _)) (𝟙 _) ≤ ε` 를 즉시 해결.
* `verify_comp`: 합성 보존 목표 `d (F.map (g ≫ f)) ((F.map g) ≫ (F.map f)) ≤ ε` 를
  `simp`‐전개 → 수치 계산(`norm_num`) → 선형 부등식(`linarith`)으로 순차 해결.
-/

namespace CatPrism.Tactics

/--  
`verify_id` — 실제로는 거의 항상 `simp` 한 방으로 끝나지만,  
`Δzero` 같이 우변이 `0`인 상황을 포함해 세 단계를 시도한다.  
-/
elab "verify_id" : tactic => do
  evalTactic (← `(tactic|
    first
      | simp                              -- `d 0 0 ≤ ε` → `simp`면 끝
      | apply le_of_eq; simp              -- 0 ≤ ε 꼴인데 = 증명만 필요한 경우
      | linarith                          -- 남은 단순 실수 부등식
  ))

/--  
`verify_comp` — 합성 보존 부등식 자동 증명.  
1. `Category.assoc`, `id_comp`, `comp_id` 등을 `simp`로 정리.  
2. 정의가 숨겨진 메트릭(PhaseDist·LengthDist·Δzero 등)을 `unfold` + `simp`.  
3. 수치식이 남으면 `norm_num`; 일반 선형(또는 0 ≤ …)은 `linarith`.  
-/
elab "verify_comp" : tactic => do
  evalTactic (← `(tactic|
    -- 1️⃣ 기본 범주 동등식 정리, 2️⃣ 메트릭 정의 전개, 3️⃣ 수치/선형 목표 해결
    (try simp only [Category.assoc, Category.id_comp, Category.comp_id] at * <;> simp at *) ;
    (try simp at *) ;
    (first
      | norm_num
      | linarith
      | apply le_of_eq; simp)            -- 예: Δzero(…) = 0 경우
  ))

end CatPrism.Tactics

