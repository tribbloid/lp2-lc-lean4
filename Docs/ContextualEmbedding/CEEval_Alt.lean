import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

open Ty

namespace STLCCtx

inductive Val : Ctx -> Ty -> Type where
  | CStar {ctx : Ctx} : Val ctx Unit
  | CLam {ctx : Ctx} {input output : Ty}
      (body : ProxyTop (ctx :/: input) input ->
        STLCCtx (ctx :/: input) output) :
      Val ctx (input :-> output)

/-- Contextually embedded value syntax with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val Ctx.Empty ty

end STLCCtx

end ContextualEmbedding.CE
