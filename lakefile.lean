import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso.git"@"v4.17.0"
require PhysLean from git "https://github.com/HEPLean/PhysLean"@"master"

package "Notes" where
  -- add package configuration options here

lean_lib Notes where
  -- add library configuration options here

@[default_target]
lean_exe notes where
  root := `Notes
