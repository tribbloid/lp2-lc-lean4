import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util

structure Indices : Type 2 where
  Index : Type 1
  getTRef (index : Index) : URef
  inc (index : Index) : Index -- TODO: for intrinsically typed AST binder this should be "Index -> Typ -> Index"

namespace Indices

/-- Naive PHOAS binding using an unknown type directly as input; `inc` does nothing. -/
abbrev Free : Indices := {Index := Type, getTRef := id, inc := λ T => T}

/--
Every new binder mixes in a tagged Unit.
At first the binder body may lack uniformity. It has to be verified first in semantics:

substitute (body (.inr .unit)) v == body (.inl v)
 -/
abbrev FreeOrUnit : Indices := {Index := Type, getTRef := id, inc := λ T => T ⊕ Unit}

/-- A proxy whose type records a lexical context slot. -/
inductive SerialProxy : Nat → URef where
| only {C : Nat} : SerialProxy C

/-- De Bruijn serial: index is fixed and incremental for every binder position-/
abbrev Serial : Indices := {
  Index := ULift.{1} Nat
  getTRef := λ t => SerialProxy t.down
  inc := λ t => ⟨t.down + 1⟩
}

end Indices

structure Parameters extends HasByteCode where
  I: Indices
  index: I.Index

namespace Parameters
section variable (this : Parameters)

abbrev TRef := this.I.getTRef this.index

abbrev Next := {this with index := this.I.inc this.index}

/-- A witness that a context is reachable by extending an earlier context. -/
inductive Under (base : Parameters) : Parameters → Type 2 where
| same : Under base base
| lower {p2} (prev : Under base p2) : Under base p2.Next

def Under.sourceIndex {base target} (self : Under base target) : target.I.Index :=
  match self with
  | .same => base.index
  | .lower prev => prev.sourceIndex

end

end Parameters

end Lp2lc.Active.Util
