import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Next.Util

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util

namespace Source

abbrev Typ (Data : TData) :=
  ∀ Carrier : TIndex, AST.Typ (Free.mk Carrier Data)

abbrev Trm (Data : TData) :=
  ∀ Carrier : TIndex, AST.Trm (Free.mk Carrier Data)

abbrev Val (Data : TData) :=
  ∀ Carrier : TIndex, AST.Val (Free.mk Carrier Data)

end Source

namespace Typ

/-- Rebuilds type syntax over another carrier without converting terms or binders. -/
def recarrier {Source Target : Free} (self : AST.Typ Source) : AST.Typ Target :=
  match self with
  | .primitive => .primitive
  | .fn tIn tOut => .fn (recarrier tIn) (recarrier tOut)

end Typ

end Lp2lc.Active.STLC.AST

namespace Lp2lc.Next.STLC

open Lp2lc.Active.Util (Free)
open Lp2lc.Active.STLC
open Lp2lc.Next.Util (UIdEquiv)
open Lp2lc.Next.Util.Free (Fixpoint WithEv)

/-- Owns the concrete receipt bridge used by runtime term references. -/
class ExeEnv (F : Free) where
  trm2valCtx : Fixpoint F AST.Trm2Val

namespace ExeEnv

abbrev CVar {F : Free} (env : ExeEnv F) : Free :=
  WithEv F env.trm2valCtx.toHasEv

end ExeEnv

/-- Owns the typing bridge for runtime receipts and covers every accepted reference. -/
class BuildEnv (F : Free) extends ExeEnv F where
  trm2typCtx :
    UIdEquiv (ExeEnv.CVar toExeEnv).Carrier
      (λ _evidence => AST.Trm2Typ (ExeEnv.CVar toExeEnv))
  coverage : ∀ cvar, trm2typCtx.Ev cvar

namespace BuildEnv

abbrev CTyp {F : Free} (env : BuildEnv F) : Free :=
  WithEv (ExeEnv.CVar env.toExeEnv) env.trm2typCtx.toHasEv

end BuildEnv

end Lp2lc.Next.STLC
