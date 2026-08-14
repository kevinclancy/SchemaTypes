import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «SchemaTypesLean» where
  -- add package configuration options here

lean_lib «SchemaTypesLean» where
  -- add library configuration options here

@[default_target]
lean_exe «schematypeslean» where
  root := `Main
