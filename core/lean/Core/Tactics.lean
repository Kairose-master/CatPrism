import Mathlib.Tactic

macro "verify_id" : tactic => `(tactic| simp)

macro "verify_comp" : tactic => `(tactic| simp)
