import Lean
import Lean.Elab.Tactic
import Lean.Meta

open Lean Elab Tactic Meta

elab "show_type_of " n:ident : tactic =>
  withMainContext do
    let ctx ← getLCtx
    match ctx.findFromUserName? n.getId with
    | none => throwError "unknown identifier '{n}'"
    | some decl =>
      let type ← instantiateMVars decl.type
      logInfo m!"The type of {n} is: {type}"


example (a b : Nat) (h : a = b) : b = a := by
  show_type_of a
  show_type_of h
  exact Eq.symm h
