import Lake
open Lake DSL

package «lean4-example» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

@[default_target]
lean_lib «Lean4Example» {
  -- add library configuration options here
}
