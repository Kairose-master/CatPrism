import CatPrism

def IdTest : EpsFunctor (d := fun _ _ _ => (0 : ℝ)) 0 := by
  refine ⟨(fun x => x), (fun f => f), ?_, ?_⟩
  · intro A B C f g; simp
  · intro A; simp

#eval 1
