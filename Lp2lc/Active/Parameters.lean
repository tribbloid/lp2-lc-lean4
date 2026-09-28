import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util

/-- Syntax contexts and their successor operation; lexical indices are distinct from runtime value receipts. -/
structure Parameters extends HasByteCode where
  TIndex : UCarrier -- lexical context/index
  index : TIndex
  indexInc : TIndex → TIndex

namespace Parameters
section variable (this : Parameters)

/-- A proxy tied to an index type, so it survives updates to a Parameters context. -/
inductive IndexProxy (Index : UCarrier) : Index → Type where
| only {C : Index} : IndexProxy Index C

abbrev Proxy := IndexProxy this.TIndex

def TRef : Type := this.Proxy this.index

abbrev Next : Parameters :=
  {this with index := this.indexInc this.index}

def TRefNext : Type := this.Next.TRef

/-- An erased witness that a context is reachable by extending an earlier context. -/
inductive Under (base : Parameters) : Parameters → Prop where
| same : Under base base
| lower {p2} (prev : Under base p2) : Under base p2.Next

end
end Parameters

end Lp2lc.Active.Util
