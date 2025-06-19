import Lake
open Lake DSL

package CatPrism

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.21.0-rc2"

@[default_target]
lean_lib Core

lean_lib CatPrism_examples
