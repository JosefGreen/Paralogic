import Lake
open Lake DSL

package «paralogic» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

@[default_target]
lean_lib Paralogic where
  srcDir := "src"

lean_exe paralogic where
  root := `Main
  srcDir := "src"
