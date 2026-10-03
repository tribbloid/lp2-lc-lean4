import «Lp2lc».Active.Util

namespace Lp2lc.Active.Util

structure Parameters extends HasByteCode where
  TRef : URef
  TRefInc : URef -> URef

namespace Parameters
section variable (this : Parameters)

abbrev TRefNext : URef := this.TRefInc this.TRef

abbrev Next : Parameters := {this with TRef := this.TRefNext}

/-- A witness that a context is reachable by extending an earlier context. -/
inductive Under (base : Parameters) : Parameters → Type 1 where
| same : Under base base
| lower {p2} (prev : Under base p2) : Under base p2.Next

end

namespace Under

def shift {base target} (self : Under base target) -- TODO replace this by a tactic
    (inc : (refs : URef) → refs → target.TRefInc refs) (carrier : base.TRef) : target.TRef :=
  match self with
  | .same => carrier
  | .lower prev => inc _ (prev.shift inc carrier)

end Under
end Parameters

-- Rule: do not change order

/-- Simplified parameters whose reference carrier is a dependent proxy of the lexical index. -/
structure CtxEmbedding extends HasByteCode where
  TIndex : URef -- lexical context/index
  index : TIndex
  indexInc : TIndex → TIndex

namespace CtxEmbedding
section variable (this : CtxEmbedding)

/-- A proxy whose type records a lexical context slot. -/
inductive ProxyOf : this.TIndex → Type where
| only {C : this.TIndex} : ProxyOf C

abbrev Proxy := this.ProxyOf this.index

def TRef : Type := this.Proxy

abbrev Next : CtxEmbedding :=
  {this with index := this.indexInc this.index}

/-- Converts the lexical index and its proxy family to parameters. -/
abbrev toParameters : Parameters :=
  {
    B := this.B
    TRef := this.TRef
    TRefInc := λ _ => this.Next.TRef
  }

end

abbrev Serial (index : Nat := 0) : CtxEmbedding := {TIndex := Nat, index := index, B := String, indexInc := Nat.succ }

-- Rule: these are ground truth rules and must be maintained at all cost
theorem equivariance(this : CtxEmbedding): this.Next.toParemeters = this.toParameters.Next := sorry

def p0 := (Serial 0).toParameters

#guard p0.Next = (Serial 1).toParameters
#guard p0.Next.Next = (Serial 2).toParameters
#guard p0.Next.Next.Next = (Serial 3).toParameters
#guard p0.Next.Next.Next.Next = (Serial 4).toParameters
#guard p0.Next.Next.Next.Next.Next = (Serial 5).toParameters


end CtxEmbedding

end Lp2lc.Active.Util
