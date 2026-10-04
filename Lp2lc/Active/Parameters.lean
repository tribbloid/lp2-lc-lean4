import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util

structure Indices where
  Index : Type u
  getTRef : Index -> URef
  inc : Index -> Index -- TODO: for intrinsically typed AST binder this should be "Index -> Typ -> Index"

namespace Indices

abbrev Raw : Indices := {Index := Type, getTRef := id, inc := λ T => T ⊕ Unit}

/-- A proxy whose type records a lexical context slot. -/
inductive ProxyOf : Nat → Type where
| only {C : Nat} : ProxyOf C

abbrev Serial : Indices := {Index := Nat, getTRef := λ t => ProxyOf t, inc := λ t => t + 1}

end Indices

structure Parameters (I: Indices) extends HasByteCode where
  index: I.Index

namespace Parameters
section variable (this : Parameters I)

abbrev Next : Parameters I := {this with index := I.inc this.index}

/-- A witness that a context is reachable by extending an earlier context. -/
inductive Under (base : Parameters I) : Parameters I → Type (max 1 u) where
| same : Under base base
| lower {p2} (prev : Under base p2) : Under base p2.Next

end

end Parameters

end Lp2lc.Active.Util
