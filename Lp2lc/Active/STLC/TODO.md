# High Priority

## Certified AST

PHOAS definition have many contradicting traits that makes it difficult to be used in proof:

- idiomatic form is always invariant: "recarrier" is impossible
- contravariant form (where .ref is flexible) => AST {TrmOrTyp} <:< AST {Trm} is absurd: AST.ref {TrmOrTyp} can't reify to value
- covariant form (where .lam is flexible) => AST {Trm} <:< AST {TrmOrTyp} works but demand parametricity of AST.lam body
  - this parametricity is built-in if AST.lam body is generated from expression with de Bruijn variable, this again make "recarrier" & proof very long, negating all advantages

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

\`\`\`
