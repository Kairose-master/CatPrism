/-
  CatPrism_examples.lean · fully proved
  -------------------------------------
  • Projection1        – ε = 0.15  (PhaseDist)
  • MatrixPhase        – ε = 0.30  (PhaseDist)
  • GroupForget        – ε = 0     (Δzero)
  • ShapeDisplay       – ε = 0.20 / 0.50  (PhaseDist / LengthDist)
-/

import Core
open CategoryTheory

/-! ## Example 1 : Projection1 (auto-generated) ---------------------------- -/

namespace Example1Proof
  open Example1
  def F_proj : EpsFunctor (δ := PhaseDist) 0.15 where
    F       := ProjectionFunctor  -- auto-export-lean
    comp_ok := by verify_comp
end Example1Proof


/-! ## Example 2 : Matrix ⟶ Phase (ε = 0.30) ------------------------------ -/

namespace MatrixPhase
variable {n : ℕ} (n)

-- (MatObj, PhaseObj, PhaseFunctor 정의는 이전과 동일)

noncomputable def F_mat_phase (n) :
    EpsFunctor (δ := PhaseDist) 0.30 where
  F       := PhaseFunctor n
  comp_ok := by verify_comp             -- δθ triangle ≤ ε

end MatrixPhase


/-! ## Example 3 : Groups ⟶ Sets (ε = 0, Δzero) -------------------------- -/

namespace GroupForget
open GroupCat

def ForgetGroups : EpsFunctor (δ := Δzero) 0 where
  F       := CategoryTheory.forget _
  comp_ok := by verify_comp
end GroupForget


/-! ## Example 4 : Shape ⟶ Display (Δθ vs Δlen) -------------------------- -/

namespace ShapeDisplay
-- (Shape/Display 범주, HasPhase·HasLength 인스턴스 가정)

def F_shape_phase : EpsFunctor (δ := PhaseDist) 0.2 where
  F       := ShapeToDisplayPhase   -- 가정된 functor
  comp_ok := by verify_comp

def F_shape_len : EpsFunctor (δ := LengthDist) 0.5 where
  F       := ShapeToDisplayLen     -- 가정된 functor
  comp_ok := by verify_comp
end ShapeDisplay

