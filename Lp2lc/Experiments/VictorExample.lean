
structure Var : Type where
  d: Nat

abbrev Function := Var -> Unit

inductive LLam : Function -> Type where

inductive HLam where

/-
explanation:
- f: fuunction
- d: de bruijn index
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
def toHOAS (fuel: Nat)(d: Nat) (l: LLam f) (Ctx: Type) : (Type) × (Function)  := sorry
