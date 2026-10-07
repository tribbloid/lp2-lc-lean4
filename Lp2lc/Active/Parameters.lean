import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util

structure Indices where
  Index : Type u
  getTRef : Index -> URef
  inc : Index -> Index -- TODO: for intrinsically typed AST binder this should be "Index -> Typ -> Index"

namespace Indices

/-- naive PHOAS binding using unknown type directly as input, inc does nothign-/
abbrev Free : Indices := {Index := Type, getTRef := id, inc := λ T => T}

/--
Every new binder mixin a tagged Unit.
At first the binder body may lack uniformity. It has to be verified first in semantics:

substitute (body (.inr .unit)) v == body (.inl v)
 -/
abbrev FreeOrUnit : Indices := {Index := Type, getTRef := id, inc := λ T => T ⊕ Unit}

/-- A proxy whose type records a lexical context slot. -/
inductive SerialProxy : Nat → Type where
| only {C : Nat} : SerialProxy C

/-- De Bruijn serial: index is fixed and incremental for every binder position-/
abbrev Serial : Indices := {Index := Nat, getTRef := λ t => SerialProxy t, inc := λ t => t + 1}

end Indices

structure Parameters extends HasByteCode where
  I: Indices
  index: I.Index

namespace Parameters
section variable (this : Parameters)

abbrev TRef := this.I.getTRef this.index

abbrev Next := {this with index := this.I.inc this.index}

/-- A witness that a context is reachable by extending an earlier context. -/
inductive Under (base : Parameters) : Parameters → Type 1 where
| same : Under base base
| lower {p2} (prev : Under base p2) : Under base p2.Next

def Under.sourceIndex {base target} (self : Under base target) : target.I.Index :=
  match self with
  | .same => base.index
  | .lower prev => prev.sourceIndex

end

end Parameters

end Lp2lc.Active.Util
