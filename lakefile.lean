import Lake
open Lake DSL

package «paralogic» where
  version := v!"0.2.0"

@[default_target]
lean_lib Paralogic where
  srcDir := "src"

lean_exe paralogic where
  root := `Main
  srcDir := "src"
