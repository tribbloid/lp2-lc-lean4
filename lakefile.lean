import Lake
open Lake DSL

package «lp2lc» where
  -- add package configuration options here

-- lean_lib «Lp2lc» where
--   -- add library configuration options here

lean_lib «Spike» where
  -- add library configuration options here

lean_lib «LeanCompiler» where
  -- add library configuration options here

lean_lib «Tests» where
  -- add library configuration options here

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "v4.29.0"

require iris from git
  "https://github.com/leanprover-community/iris-lean.git" @ "master"
