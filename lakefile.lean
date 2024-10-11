import Lake
open Lake DSL

package "lean-test" where
  version := v!"0.1.0"

lean_lib «LeanTest» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-test" where
  root := `Main
