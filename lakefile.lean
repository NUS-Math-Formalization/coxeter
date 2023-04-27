import Lake
open Lake DSL

package «coxeter4» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Coxeter4» {
  -- add any library configuration options here
}
