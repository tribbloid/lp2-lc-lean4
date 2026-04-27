import Lake
open Lake DSL

package «Lp2lc» where

@[default_target]
lean_lib «Lp2lc» where

@[default_target] -- compiled but should never publish
lean_lib «Tests» where

lean_lib «Spike» where

lean_lib «LeanCompiler» where


require aesop from git
  "https://github.com/leanprover-community/aesop" @ "v4.29.0"

require iris from git
  "https://github.com/leanprover-community/iris-lean.git" @ "master" / "Iris"
