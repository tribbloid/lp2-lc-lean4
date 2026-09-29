import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util

structure Parameters extends HasByteCode where
  TRef : URef
  TRefInc : URef -> URef

namespace Parameters
section variable (this : Parameters)

abbrev Next : Parameters :=
  {this with TRef := this.TRefInc this.TRef}

/-- An erased witness that a context is reachable by extending an earlier context. -/
inductive Under (base : Parameters) : Parameters → Prop where
| same : Under base base
| lower {p2} (prev : Under base p2) : Under base p2.Next

end
end Parameters

/-- Syntax contexts and their successor operation; lexical indices are distinct from runtime value receipts. -/
structure CtxEmbedding extends HasByteCode where
  TIndex : URef -- lexical context/index
  index : TIndex
  indexInc : TIndex → TIndex

namespace CtxEmbedding
section variable (this : CtxEmbedding)

/-- A proxy whose type records a lexical context slot. -/
inductive IndexProxy (Index : URef) : Index → Type where
| only {C : Index} : IndexProxy Index C

abbrev Proxy := IndexProxy this.TIndex

def TRef : Type := this.Proxy this.index

abbrev Next : CtxEmbedding :=
  {this with index := this.indexInc this.index}

def TRefNext : Type := this.Next.TRef

/-- An erased witness that a context is reachable by extending an earlier context. -/
inductive Under (base : CtxEmbedding) : CtxEmbedding → Prop where
| same : Under base base
| lower {p2} (prev : Under base p2) : Under base p2.Next

end

/-- Builds parameters whose successor retains prior references and adds the next lexical slot. -/
def toParameters (this : CtxEmbedding) : Parameters :=
  { B := this.B
    TRef := this.TRef
    TRefInc := λ TRef => TRef ⊕ this.TRefNext }

instance : Coe CtxEmbedding Parameters where -- TODO: not need, explicit conversion is good enough
  coe := toParameters

abbrev DeBruijn : CtxEmbedding := {TIndex := Nat, index := 0, B := String, indexInc := Nat.succ }

end CtxEmbedding

end Lp2lc.Active.Util
