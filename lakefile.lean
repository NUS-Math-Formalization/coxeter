import Lake
open Lake DSL

package Coxeter {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "trivial1711-coxeter-groups-all"


meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
-- require mathlib from git
--   "https://gitee.com/zzsj01/mathlib4.git"

@[default_target]
lean_lib Coxeter {
  -- add any library configuration options here
}
