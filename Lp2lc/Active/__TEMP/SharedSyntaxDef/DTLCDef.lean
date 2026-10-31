import «Lp2lc».Active.Parameters

/-!
An extensible version of DTLC's syntax. Common constructors are declared once in `AST`;
their recursive children and binders use the same extension as their parent.

Each extension tag specifies its result label and ordered child labels. `Args` supplies
exactly those children, so extensions remain strictly positive and cannot mix syntax labels.
The empty extension `NoExtra` recovers the DTLC grammar as `AST NoExtra`.

This signature covers additional cases with finitely many AST children in the current
context, including all current DSub cases. Tags can also carry nonrecursive payloads.
New binding forms or children in different contexts would require extending the signature
representation. Existing DTLC/DSub modules are left untouched.
-/

namespace Lp2lc.Active.__TEMP.SharedSyntaxDef.DTLC.Pre

open Lp2lc.Active.Util

abbrev Extension := (label : Label) → (children : List Label) → Type

inductive NoExtra : (label : Label) → (children : List Label) → Type

mutual

inductive Binder (extension : Extension) : (P : Parameters) → (label : Label) → UAST where
/-- Internal construction callback; open it only through `Binder.apply` under the index
encoding's contract. UId opens at `.inr ()` and substitutes receipts structurally;
serial binders receive their sole context proxy. -/
| private body {P label} (body : (carrier : P.Next.TRef) → AST extension P.Next label) :
    Binder extension P label

inductive AST (extension : Extension) : (P : Parameters) → (label : Label) → UAST where
| TLit {P} : AST extension P .typ
| lit {P} (repr : P.B) : AST extension P .val
| TFn {P} (tIn : AST extension P .typ) (tOut : Binder extension P .typ) : AST extension P .typ
| fn {P} (tIn : AST extension P .typ) (body : Binder extension P .trm) : AST extension P .val
| fnPrimitive {P} (tOut : Binder extension P .typ) (op : (repr : P.B) → AST extension P .val) :
    AST extension P .val
| ref {P P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST extension P .trm
| val {P} (value : AST extension P .val) : AST extension P .trm
| apply {P} (fn arg : AST extension P .trm) : AST extension P .trm
| extra {P label children} (tag : extension label children)
    (args : Args extension P children) : AST extension P label

/-- A heterogeneous list whose indices fix each child's context and syntax label. -/
inductive Args (extension : Extension) : (P : Parameters) → (labels : List Label) → UAST where
| nil {P} : Args extension P []
| cons {P label labels} (head : AST extension P label) (tail : Args extension P labels) :
    Args extension P (label :: labels)

end

namespace Binder

variable {extension : Extension} {P : Parameters} {label : Label}

def mk (body : (carrier : P.Next.TRef) → AST extension P.Next label) : Binder extension P label :=
  .body body

/-- Open a binder under its index encoding's reference contract. -/
def apply (self : Binder extension P label) (carrier : P.Next.TRef) : AST extension P.Next label :=
  match self with
  | .body code => code carrier

end Binder

end Lp2lc.Active.__TEMP.SharedSyntaxDef.DTLC.Pre
