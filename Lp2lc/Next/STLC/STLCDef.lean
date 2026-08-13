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
open Lp2lc.Next.Util.Free (Fixpoint FixpointCtor WithEv)

/-- Owns the bridge constructor shared by concrete STLC contexts. -/
class ExeEnv (F : Free) where
  ctor : FixpointCtor F

namespace ExeEnv

def trm2valCtx {F : Free} (env : ExeEnv F) : Fixpoint F AST.Trm2Val :=
  @FixpointCtor.mkFixpoint F env.ctor AST.Trm2Val

abbrev CVar {F : Free} (env : ExeEnv F) : Free :=
  WithEv F env.trm2valCtx.toHasEv

end ExeEnv

/-- Adds the compile-time typing context to an execution environment. -/
class BuildEnv (F : Free) extends ExeEnv F

namespace BuildEnv

def trm2typCtx {F : Free} (env : BuildEnv F) : Fixpoint F AST.Trm2Typ :=
  @FixpointCtor.mkFixpoint F env.ctor AST.Trm2Typ

abbrev CTyp {F : Free} (env : BuildEnv F) : Free :=
  WithEv F env.trm2typCtx.toHasEv

end BuildEnv

end Lp2lc.Next.STLC
