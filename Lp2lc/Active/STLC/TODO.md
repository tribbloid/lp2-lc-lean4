# High Priority

## Parallel Structural Induction? Does it eliminate the need for parametricity axiom?

- both eval & infer use AST that can refer to everything
- a single function to produce a bundle of both results:
- since DOT has (mutual) recursion, there is no guarantee that their execution are identical at low level, but they must be related. (this is also a reason that fn type should always carry types of both input & output)

```lean
structure Parallel
  typ: AST.Typ
  inferVal: AST.Val -> AST.Typ -- lambda `val => val.infer`
  relatedSafeVals UIdRefs {x // inferVal x <= typ } -- 1 type can have many values so this has to be a refs
  
  safety: (c : relatedResult.UId) -> (inferResult (relatedResult.get c) <= typ) 
```

- the last member is multiple values related to a type, with their safety proof

The vulnerability of forging Val from Typ UId is thwarted not by using different UId types (UIdEquiv can get/inv Parallel directly), but by **tracking lineage/dependency of construction**

- when constructing val, typ is invisible ()
- when constructing typ, val is invisible (cannot see result of execution iin compiletime)

## Certified AST

Update: `AST.fn` now stores first-order `Binder` syntax with a distinguished
newest slot. This makes receipt-inspecting lambda bodies unrepresentable;
`AST.recarrier` is retained as the structural operation used by binder
specialization. The tradeoff notes below describe the earlier PHOAS encoding.

PHOAS definition have many contradicting traits that makes it difficult to be used in proof:

- idiomatic form is always invariant: "recarrier" is impossible
- contravariant form (where .ref is flexible) => AST {TrmOrTyp} <:< AST {Trm} is absurd: AST.ref {TrmOrTyp} can't reify to value
- covariant form (where .fn is flexible) => AST {Trm} <:< AST {TrmOrTyp} works but demand parametricity of AST.fn body
  - this parametricity is built-in if AST.fn body is generated from expression with de Bruijn variable, this again make "recarrier" & proof very long, negating all advantages

## Verdicts

- Single carrier type for all AST, no more "recarrier"
  - UIdEquiv that uses this carrier must be able to save everything (Val/Typ/Proof etc.)
- compilation can process `Val ⊕ Typ` (referring to breakpoint free vars and bounded vars in a subsection respectively)

* eval can only process `Val` , to run (`AST.ref u1).eval` successfully, u1 must be a subtype ({x : P.C // Ev x})
* the 2 parts x and Ev x can be stored in different places, Ev x may be flat
* this allows AST ready for eval to be broken into 2 parts:

```lean
structure Ref
  body: P.C

inductive AST {TRef : Type}: Parameters -> Label where
  .ref (v: TRef)

structure Certified {TRef : Type} (ast : AST TRef P L)
  .certify : P.C -> {x : PC // Ev x} -- This is not tight enough
```

what about this:

\`\`\`

structure CAST L

P : Parameters

ast: AST P L -- floating

## Breakpoint compilation is too hard? Start with only closed terms
