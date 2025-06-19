import Lake
open Lake DSL

package CatPrism

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "675fd38969d2d004640fe02425a4128acc9c9f4a"

@[default_target]
lean_lib Core

lean_lib CatPrism_examples
