import Lake
open Lake DSL

package «Lp2lc» where

@[default_target]
lean_lib «Lp2lc» where

@[default_target] -- compiled but should never publish
lean_lib «Tests» where

@[default_target] -- compiled but should never publish
lean_lib «Docs» where
  srcDir := "Docs"
  roots := #[`ContextualEmbedding, `LeanCompiler, `Phoas]

lean_lib «Spike» where

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "v4.32.1"

require iris from git
  "https://github.com/leanprover-community/iris-lean.git" @ "master" / "Iris"
