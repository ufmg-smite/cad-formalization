import Lake

open Lake DSL

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

package Cad

@[default_target]
lean_lib Cad
