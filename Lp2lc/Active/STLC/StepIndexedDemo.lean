import Iris.BI

namespace Lp2lc.Active.STLC.StepIndexedDemo

open Iris
open Iris.OFE
open Iris.BI

section

variable {PROP : Type _} [BI PROP] [BILaterContractive PROP]

def negative_body : PROP -c> PROP where
  f rec := iprop(▷ ¬ rec)
  contractive := by
    refine ⟨?_⟩
    intro n P Q h
    exact Contractive.distLater_dist (f := Iris.BI.BIBase.later (PROP := PROP)) fun m hm =>
      BI.imp_ne.ne (h m hm) Dist.rfl

def negative : PROP := negative_body.fixpoint

theorem negative_unfold :
    negative (PROP := PROP) ≡ iprop(▷ ¬ negative (PROP := PROP)) :=
  fixpoint_unfold (negative_body (PROP := PROP))

theorem negative_induction
    (P : PROP → Prop)
    (hproper : ∀ Q R : PROP, Q ≡ R → P Q → P R)
    (hbase : P default)
    (hstep : ∀ Q, P Q → P (negative_body (PROP := PROP) Q))
    (hlim : LimitPreserving P) :
    P (negative (PROP := PROP)) := by
  simpa [negative] using
    (OFE.ContractiveHom.fixpoint_ind (f := negative_body (PROP := PROP))
      P hproper default hbase hstep hlim)

end

end Lp2lc.Active.STLC.StepIndexedDemo
