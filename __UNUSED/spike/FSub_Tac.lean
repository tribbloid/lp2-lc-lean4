
import Lean
import «Lp2lc».active.FSub_Gemini_Def

open Lean Elab Tactic Meta Term
open Lp2lc.FSub

-- Alternative implementation as term elaborator
elab "gather_var_term" : term => do
  logInfo "gather_var_term: Computing variables from context"

  -- Create a simple TermElabM version that doesn't use TacticM
  let lctx ← getLCtx
  let mut varCount := 0

  for localDecl in lctx do
    if localDecl.isImplementationDetail then continue
    let declType ← inferType (Lean.mkFVar localDecl.fvarId)
    if ← isDefEq declType (Lean.mkConst ``Var) then
      varCount := varCount + 1
      logInfo s!"gather_var_term: Found Var declaration: {localDecl.userName}"

  logInfo s!"gather_var_term: Result computed with {varCount} variables"

  -- Return empty set as proper Expr
  return Lean.mkApp (Lean.mkConst ``Finset.empty [levelZero]) (Lean.mkConst ``Var)

-- Example using the term elaborator
example (_x _y : Var) (_t : typ) : Vars :=
  gather_var_term
