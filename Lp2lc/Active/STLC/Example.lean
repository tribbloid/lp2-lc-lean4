import «Lp2lc».Active.STLC.Def


namespace Lp2lc.Active.STLC

namespace Example

  inductive ActualAST : Rep where
  | self: AST ActualAST w -> ActualAST w -- TODO: why can't w be moved to be before the colon?

  #check ActualAST

  -- real expressions of ActualAST in STLC
  example :=
    let k1 : LC.AST ActualAST .typ := .anyT -- LC
    let k2 : AST ActualAST .typ := -- STLC(LC)
      let k1View : AST ActualAST .typ := .backbone k1
      .fnT (.self k1View) (.self k1View)
    let _ : ActualAST .typ := .self k2 -- fixpoint of STLC(LC)
    Unit

  -- more generic STLC expressions in any type system that uses STLC as backbone
  -- namely, mk ensures that Typ F always has a representation in F
  -- the reverse (F -> Typ F) is not true (e.g. for System F)

  -- consequently, generic, extendable inductive proof need stronger conditions
  -- see Example in SysF for what these conditions look like
  example (F: Rep) (mk: ∀ {w: Which}, AST F w -> F w) :=
    let k1 : LC.AST F .typ := .anyT -- LC
    let k2 : AST F .typ := -- STLC(LC)
      let k1View : AST F .typ := .backbone k1
      .fnT (mk k1View) (mk k1View)
    let _ : F .typ := mk k2 -- fixpoint of STLC(LC)
    Unit

end Example

end Lp2lc.Active.STLC
