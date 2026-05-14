import Lake
open Lake DSL

package «concert» where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0"

@[default_target]
lean_lib «ConCert» where

@[test_driver]
lean_exe «concert-tests» where
  root := `Tests
