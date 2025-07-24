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

elab "show_types_of_all_vars" : tactic =>
  withMainContext do
    logInfo "Types of all variables in context:"
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      let type := decl.type
      logInfo m!"  {decl.userName}: {type}"

example (x y : String) (p : x = y) : y = x := by
  show_types_of_all_vars
  exact Eq.symm p


elab "show_types_of_all_vars_alt" : tactic =>
  withMainContext do
    let mut typeList : Array String := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      let type := decl.type
      let name := m!"  {decl.userName}: {type}"
      typeList := typeList.push (← name.toString)
    let multiLineString := "Types of all variables in context:\n" ++ String.intercalate "\n" typeList.toList
    logInfo multiLineString

example (x y : String) (p : x = y) : y = x := by
  show_types_of_all_vars_alt
  exact Eq.symm p


elab "show_types_of_all_vars_monadic" : tactic =>
  withMainContext (
    logInfo (m!"Types of all variables in context (monadic):") >>= fun _ =>
    getLCtx >>= fun lctx =>
      lctx.forM fun decl =>
        if decl.isImplementationDetail then
          pure ()
        else
          instantiateMVars decl.type >>= fun type =>
          logInfo m!"  {decl.userName}: {type}"
  )

example (i j : Bool) (q : i = j) : j = i := by
  show_types_of_all_vars_monadic
  exact Eq.symm q

-- Monadic version without do blocks or for loops
elab "show_types_of_all_vars_pure_monadic" : tactic =>
  withMainContext (
    logInfo "Types of all variables in context (pure monadic):" *>
    getLCtx >>= fun lctx =>
    lctx.foldlM (fun _ decl =>
      if decl.isImplementationDetail then
        pure ()
      else
        instantiateMVars decl.type >>= fun type =>
        logInfo m!"  {decl.userName}: {type}"
    ) ()
  )

example (m n : Int) (r : m = n) : n = m := by
  show_types_of_all_vars_pure_monadic
  exact Eq.symm r
