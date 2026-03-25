import Iris.BI

namespace Lp2lc.Active.STLC.StepIndexDemo_partiallyCorrect

open Iris
open Iris.OFE
open Iris.BI

section

variable {PROP : Type _} [BI PROP] [BILaterContractive PROP]

def partial_correct_body (post : PROP) : PROP -c> PROP where
  f rec := iprop(post ∨ ▷ rec)
  contractive := by
    refine ⟨?_⟩
    intro n P Q h
    exact BI.or_ne.ne Dist.rfl <|
      Contractive.distLater_dist (f := Iris.BI.BIBase.later (PROP := PROP)) h

def partial_correct (post : PROP) : PROP :=
  (partial_correct_body (PROP := PROP) post).fixpoint

theorem partial_correct_unfold (post : PROP) :
    partial_correct (PROP := PROP) post ≡
      iprop(post ∨ ▷ partial_correct (PROP := PROP) post) :=
  fixpoint_unfold (partial_correct_body (PROP := PROP) post)

theorem partial_correct_intro (post : PROP) :
    post ⊢ partial_correct (PROP := PROP) post :=
  BI.or_intro_l.trans
    ((BI.equiv_iff.mp (partial_correct_unfold (PROP := PROP) post)).mpr)

theorem partial_correct_valid {post : PROP} (hpost : ⊢ post) :
    ⊢ partial_correct (PROP := PROP) post :=
  hpost.trans (partial_correct_intro (PROP := PROP) post)

section

variable [BILoeb PROP]

theorem loop_partial_correct :
    ⊢ partial_correct (PROP := PROP) iprop(False) :=
  true_intro.trans <|
    BILoeb.loeb_weak <|
      BI.or_intro_r.trans
        ((BI.equiv_iff.mp (partial_correct_unfold (PROP := PROP) iprop(False))).mpr)

end

end

end Lp2lc.Active.STLC.StepIndexDemo_partiallyCorrect
