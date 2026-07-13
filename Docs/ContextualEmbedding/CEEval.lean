import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

open Ty

/-- STLC value syntax for unit and function values in a configurable context. -/
inductive Val : Ctx -> Ty -> Type where
  | Star {ctx : Ctx} : Val ctx Unit
  | Lambda {ctx : Ctx} {input output : Ty}
      (body : STLC (ctx :/: input) output) : Val ctx (input :-> output)
deriving Repr, DecidableEq

/-- STLC values with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val Ctx.Empty ty

end ContextualEmbedding.CE
