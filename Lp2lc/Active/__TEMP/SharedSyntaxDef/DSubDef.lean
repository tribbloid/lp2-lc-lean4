import «Lp2lc».Active.__TEMP.SharedSyntaxDef.DTLCDef

/-!
DSub adds only five signatures to the shared DTLC syntax. For example,
`Extra.TMember : Extra .typ [.typ, .typ]` fixes its result to a type and its children
to exactly two types; `Extra.TSel` instead requires one value child.

The typed, reducible abbreviations in `AST` restore the ordinary constructor interface.
`@[match_pattern]` also permits these names in patterns. They expand to the shared
`AST.extra` constructor and typed `Args`; they are not new kernel constructors.
Induction uses the shared AST's recursor and its generic extension case.
Inside common constructors, qualify extension cases as `AST.TMember`, etc.; their
child types expose the generic DTLC family rather than the DSub abbreviation.
-/

namespace Lp2lc.Active.__TEMP.SharedSyntaxDef.DSub.Pre

open Lp2lc.Active.Util

inductive Extra : (label : Label) → (children : List Label) → Type where
| TTop : Extra .typ []
| TBot : Extra .typ []
| TMember : Extra .typ [.typ, .typ]
| TSel : Extra .typ [.val]
| typeDef : Extra .val [.typ]

abbrev AST := DTLC.Pre.AST Extra
abbrev Binder := DTLC.Pre.Binder Extra

namespace AST

variable {P : Parameters}

@[match_pattern] abbrev TTop : AST P .typ := .extra .TTop .nil
@[match_pattern] abbrev TBot : AST P .typ := .extra .TBot .nil

@[match_pattern] abbrev TMember (lower upper : AST P .typ) : AST P .typ :=
  .extra .TMember (.cons lower (.cons upper .nil))

@[match_pattern] abbrev TSel (value : AST P .val) : AST P .typ :=
  .extra .TSel (.cons value .nil)

@[match_pattern] abbrev typeDef (typ : AST P .typ) : AST P .val :=
  .extra .typeDef (.cons typ .nil)

end AST

end Lp2lc.Active.__TEMP.SharedSyntaxDef.DSub.Pre
