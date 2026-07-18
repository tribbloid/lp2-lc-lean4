
structure Var : Type where
  d : Nat

inductive LLam : Type where
  | mk (f : Var -> LLam)

inductive HLam (Ctx : Type) : Type where
  | mk (f : Ctx -> Option (HLam Ctx))

abbrev Function (Ctx : Type) := (c : Ctx) -> (v : Var) -> Option (HLam Ctx)

/-
explanation:
- f: function
- d: de bruijn index ?
- Ctx: context
- Lam: lambda
- HOAS: higher-order abstract syntax
- Var: variable
- LLam: Low Lambda ???
- HLam: High Lambda ???

`toHOAS` should return the same input Ctx and a new function

for Lean4 prover:
- to circumvent termination constraint, introduce fuel
- to circumvent positivity constraint in Lean4, type parameters at negative position can be introduced
-/

/--
Pseudocode:

toHOAS d (LLam f) ctx =
  let (ctx,f) = toHOAS (d+1) (f (Var d)) (x : ctx)
  in (HLam \x -> f)
-/
def toHOAS (fuel : Nat) (d : Nat) (l : LLam) (Ctx : Type) : Type × Function Ctx :=
  match fuel with
  | 0 => (Ctx, λ _ _ => none)
  | fuel + 1 =>
      match l with
      | .mk f =>
          let (ctx, body) := toHOAS fuel (d + 1) (f { d := d }) Ctx
          (ctx, λ _ v => some (HLam.mk (λ c => body c v)))
