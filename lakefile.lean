import Lake

open Lake DSL

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

require CompPoly from
  git "https://github.com/tomaz1502/CompPoly.git" @ "divByMonic"

package Cad

@[default_target]
lean_lib Cad
