import Lake
open Lake DSL

package Coxeter {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require ssreflect from git "https://github.com/verse-lab/lean-ssr" @ "master"

-- require mathlib from git
--   "https://gitee.com/zzsj01/mathlib4.git"

@[default_target]
lean_lib Coxeter {
  -- add any library configuration options here
}
