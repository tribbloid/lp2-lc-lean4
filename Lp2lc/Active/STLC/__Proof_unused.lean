import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util


/-- Consecutive carrier changes are equivalent to their bundled composition. -/
@[simp]
theorem AST.recarrierComposability {P Q R : Parameters} {l : Label} (self : AST P l)
    (first : Parameters.CarrierMap P Q) (second : Parameters.CarrierMap Q R) :
    (self.recarrier first).recarrier second = self.recarrier (first.«then» second) := by
  induction self using AST.rec
    (motive_2 := λ P body =>
      ∀ {Q R : Parameters} (first : Parameters.CarrierMap P Q) (second : Parameters.CarrierMap Q R),
        (body.recarrier first).recarrier second = body.recarrier (first.«then» second))
    generalizing Q R with
  | primitive => rfl
  | fn tIn tOut ihIn ihOut => simp [ihIn, ihOut]
  | val value ih => simp [ih]
  | apply fnTerm arg ihFn ihArg => simp [ihFn, ihArg]
  | ref source =>
    cases source with
    | inl free => rfl
    | inr bound =>
      cases hFirst : first.mapB bound <;> simp [Parameters.CarrierMap.«then»,
        Parameters.CarrierMap.mapRef, hFirst]
  | lit repr => rfl
  | lam body tIn ihBody ihIn => simp [ihBody, ihIn]
  | mk body ihBody =>
    simp only [LamBody.recarrier]
    rw [ihBody, Parameters.CarrierMap.underBinderThen]

/-- Consecutive carrier changes beneath a lambda preserve its newest binder slot. -/
@[simp]
theorem LamBody.recarrierComposability {P Q R : Parameters} (self : LamBody P)
    (first : Parameters.CarrierMap P Q) (second : Parameters.CarrierMap Q R) :
    (self.recarrier first).recarrier second = self.recarrier (first.«then» second) := by
  cases self with
  | mk body =>
    simp only [LamBody.recarrier]
    rw [AST.recarrierComposability, Parameters.CarrierMap.underBinderThen]

/-- Generalized naturality of specialization under a subsequent carrier map. -/
def LamBody.SpecialiseNaturality {P : Parameters} (self : LamBody P) : Prop :=
  ∀ {Q R : Parameters} (first : Parameters.CarrierMap P Q) (second : Parameters.CarrierMap Q R)
    (arg : Q.F ⊕ Q.B),
    (self.specialise first arg).recarrier second =
      self.specialise (first.«then» second) (second.mapRef arg)

/-- Structural lambda specialization is natural across every carrier map. -/
theorem LamBody.specialiseNaturality {P : Parameters} (self : LamBody P) :
    self.SpecialiseNaturality := by
  intro Q R first second arg
  unfold specialise
  rw [AST.recarrierComposability, Parameters.CarrierMap.bindThen]

end STLC
