import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util

/-- Syntax contexts and their successor operation; lexical indices are distinct from runtime value receipts. -/
structure Parameters extends HasByteCode where
  TIndex : UCarrier -- lexical context/index
  index : TIndex
  nextIndex : TIndex → TIndex

namespace Parameters
section variable (this : Parameters)

abbrev Proxy := IndexProxy this.TIndex

def TRef : Type := this.Proxy this.index

abbrev Next : Parameters :=
  {this with index := this.nextIndex this.index}

def NextTRef : Type := this.Next.TRef

/-- An erased witness that a context is reachable by extending an earlier context. -/
inductive Lesser (i1 : this.TIndex) : this.TIndex → Prop where
| refl : Lesser i1 i1
| step {i2} (prior : Lesser i1 i2) : Lesser i1 ({this with index := i2}).Next.index

end
end Parameters

end Lp2lc.Active.Util
