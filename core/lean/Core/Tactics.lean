import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Core.RawPrefunctor
import Mathlib.Tactic -- `linarith`를 위해 필요

open CategoryTheory
open Lean Elab Tactic

-- `verify_id`는 이미 훌륭합니다.
elab "verify_id" : tactic => do
  evalTactic (← `(tactic|
    first
      | simp
      | apply le_of_eq; simp
      | linarith))

/--
A more robust tactic for verifying composition.
It attempts to unfold definitions and solve the goal numerically.
Full automation may require domain-specific lemmas.
-/
elab "verify_comp" : tactic => do
  evalTactic (← `(tactic|
    -- 1. 증명 목표의 형태를 단순화합니다.
    -- 예: `d (F.map (g ≫ f)) (F.map g ≫ F.map f) ≤ ε`
    simp;
    
    -- 2. 메트릭의 정의를 펼칩니다. (예: PhaseDist, LengthDist)
    -- 이는 `unfold`나 추가적인 `simp` 규칙이 필요할 수 있습니다.
    -- 예: simp [PhaseDist]
    
    -- 3. 실제 값들을 계산하여 부등식을 증명합니다.
    -- `norm_num`은 수치 계산에 강력합니다.
    try norm_num;

    -- 4. 최종적인 선형 부등식을 해결합니다.
    try linarith
  ))

