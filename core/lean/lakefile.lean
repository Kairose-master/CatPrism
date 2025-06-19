import Lake
open Lake DSL

package CatPrism

require lean from git "https://github.com/leanprover/lean4.git" @ "77cfc4d"

@[default_target]
lean_lib Core

lean_lib CatPrism_examples
