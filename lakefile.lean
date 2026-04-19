import Lake
open Lake DSL

package «Lp2lc» where

lean_lib «Lp2lc» where

lean_lib «Spike» where

lean_lib «LeanCompiler» where

lean_lib «Tests» where

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "v4.29.0"

require iris from git
  "https://github.com/leanprover-community/iris-lean.git" @ "master"
