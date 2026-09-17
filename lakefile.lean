import Lake

open Lake DSL

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

package Cad

@[default_target]
lean_lib Cad
