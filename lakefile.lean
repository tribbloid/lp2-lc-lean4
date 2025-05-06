import Lake
open Lake DSL

package «lp2lc» where
  -- add package configuration options here

lean_lib «Lp2lc» where
  -- add library configuration options here

@[default_target]
lean_exe «lp2lc» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "v4.18.0"


require batteries from
  git "https://github.com/leanprover-community/batteries" @ "v4.18.0"


require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.18.0"
