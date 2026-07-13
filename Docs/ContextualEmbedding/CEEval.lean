import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

open Ty

namespace STLC

/-- STLC value syntax for unit and function values in a configurable context. -/
inductive Val : Ctx -> Ty -> Type where
  | Star {ctx : Ctx} : Val ctx Unit
  | Lambda {ctx : Ctx} {input output : Ty}
      (body : STLC (ctx :/: input) output) : Val ctx (input :-> output)
deriving Repr, DecidableEq

/-- STLC values with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val Ctx.Empty ty

end STLC

namespace STLCCtx

inductive Val : Ctx -> Ty -> Type where
  | CStar {ctx : Ctx} : Val ctx Unit
  | CLam {ctx : Ctx} {input output : Ty}
      (body : ProxyTop (ctx :/: input) input ->
        STLCCtx (ctx :/: input) output) :
      Val ctx (input :-> output)

/-- Contextually embedded values with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val Ctx.Empty ty


end STLCCtx

end ContextualEmbedding.CE
