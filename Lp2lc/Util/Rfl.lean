import Lean

open Lean Elab Command Meta

private partial def normalize_expr (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  match e with
  | .lam n d b bi =>
      let d ← normalize_expr d
      withLocalDecl n bi d λ x => do
        let b ← normalize_expr (b.instantiate1 x)
        mkLambdaFVars #[x] b
  | .forallE n d b bi =>
      let d ← normalize_expr d
      withLocalDecl n bi d λ x => do
        let b ← normalize_expr (b.instantiate1 x)
        mkForallFVars #[x] b
  | _ =>
      reduceAll e

syntax (name := rflCmd) "#rfl " term : command

@[command_elab rflCmd] def elab_rfl_cmd : CommandElab
  | `(#rfl $t:term) =>
      withoutModifyingEnv <| runTermElabM λ _ =>
        Term.withDeclName `_rfl do
          let lhs ← Term.elabTerm t none
          Term.synthesizeSyntheticMVarsNoPostponing
          withRef t <| Meta.check lhs
          let lhs ← Term.levelMVarToParam (← instantiateMVars lhs)
          let rhs_source ←
            match lhs with
            | .const decl_name us =>
                let info ← getConstInfo decl_name
                match info.value? with
                | some _ => instantiateValueLevelParams info us
                | none => pure lhs
            | _ =>
                pure lhs
          let rhs ← withTransparency (mode := .all) <| normalize_expr rhs_source
          let lhs_fmt ← ppExpr lhs
          let rhs_fmt ← ppExpr rhs
          logInfoAt t m!"{lhs_fmt} = {rhs_fmt}"
  | _ => throwUnsupportedSyntax
