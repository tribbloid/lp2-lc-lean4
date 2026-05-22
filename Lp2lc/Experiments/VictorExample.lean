

structure LLam where

structure HLam where

/-
toHOAS d (LLam f) ctx =
  let (ctx,f) = toHOAS (d+1) (f (Var d)) (x : ctx)
  in (HLam \x -> f)

explanation:
- f: fuunction
- d: depth
- ctx: context
- Lam: lambda
- HOAS: higher-order abstract syntax
- Var: variable

(LLam f) should become a pattern matching

to circumvent positivity constraint in Lean4, type parameters at negative position can be introduced
-/
def toHOAS (d: Nat) (l: LLam) (Ctx: Type) := sorry
