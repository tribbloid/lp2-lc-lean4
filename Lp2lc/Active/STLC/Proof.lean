import Mathlib.Tactic
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.Def

/-!
This file proves soundness for simply typed lambda calculus by interpreting
terms with a step-indexed logical relation. The step index is the fuel used to
reason about functions recursively: a function is safe for `fuel` when, for
any `lessFuel ≤ fuel`, it sends semantically safe inputs to outputs that
stay safe one guarded step later.

All docstrings use short (under 5 lines) of Scala code as demonstrations.
-/

namespace Lp2lc.Active.STLC

section PHOAS

variable (TrmVar : Type)

namespace Semantic

def Safe : Nat -> Trm TrmVar -> Lp2lc.Active.STLC.Typ -> Prop
| 0, term, type =>
    Typ.AsSemantic (TrmVar := TrmVar) type term
| _ + 1, term, .base =>
    Typ.AsSemantic (TrmVar := TrmVar) .base term
| steps + 1, term, tIn :=> tOut =>
    Typ.AsSemantic (TrmVar := TrmVar) (tIn :=> tOut) term ∧
    ∀ smaller : Nat, (smaller_lt : smaller < steps + 1) ->
      ∀ argument : Trm TrmVar, Safe smaller argument tIn ->
        Later (Safe smaller (.apply term argument) tOut)
termination_by steps _ _ => steps
decreasing_by
  all_goals
    simp_wf
    omega

theorem safe_hasType {steps : Nat} {term : Trm TrmVar} {type : Lp2lc.Active.STLC.Typ} :
    Safe (TrmVar := TrmVar) steps term type ->
    Typ.AsSemantic (TrmVar := TrmVar) type term := by
  intro safe
  induction steps generalizing term type with
  | zero =>
      unfold Safe at safe
      exact safe
  | succ steps induction =>
      cases type with
      | base =>
          unfold Safe at safe
          exact safe
      | arrow tIn tOut =>
          unfold Safe at safe
          exact safe.1

theorem safe_mono {smaller larger : Nat} {term : Trm TrmVar} {type : Lp2lc.Active.STLC.Typ}
    (smaller_le : smaller ≤ larger) :
    Safe (TrmVar := TrmVar) larger term type ->
    Safe (TrmVar := TrmVar) smaller term type := by
  intro safe
  cases smaller with
  | zero =>
      unfold Safe
      exact safe_hasType (TrmVar := TrmVar) safe
  | succ smaller =>
      cases larger with
      | zero =>
          cases smaller_le
      | succ larger =>
          cases type with
          | base =>
              unfold Safe
              exact safe_hasType (TrmVar := TrmVar) safe
          | arrow tIn tOut =>
              unfold Safe at safe ⊢
              refine And.intro safe.1 ?_
              intro guardedStep guarded_lt argument argument_safe
              exact safe.2 guardedStep (lt_of_lt_of_le guarded_lt smaller_le) argument argument_safe

theorem fundamental_lemma {term : Trm TrmVar} {type : Lp2lc.Active.STLC.Typ}
    (typing : Typ.AsSemantic (TrmVar := TrmVar) type term) :
    ∀ steps : Nat, Safe (TrmVar := TrmVar) steps term type := by
  have fundamental :
      ∀ steps : Nat, ∀ {term : Trm TrmVar} {type : Lp2lc.Active.STLC.Typ},
        Typ.AsSemantic (TrmVar := TrmVar) type term ->
        Safe (TrmVar := TrmVar) steps term type := by
    intro steps
    induction steps with
    | zero =>
        intro term type typing
        unfold Safe
        exact typing
    | succ steps induction_hypothesis =>
        intro term type typing
        cases type with
        | base =>
            unfold Safe
            exact typing
        | arrow tIn tOut =>
            unfold Safe
            refine And.intro typing ?_
            intro smaller smaller_lt argument argument_safe
            refine ⟨?_⟩
            exact safe_mono (TrmVar := TrmVar)
              (Nat.lt_succ_iff.mp smaller_lt)
              (induction_hypothesis
                (term := .apply term argument)
                (type := tOut)
                (Typ.AsSemantic.apply typing (safe_hasType (TrmVar := TrmVar) argument_safe)))
  intro steps
  exact fundamental steps typing

theorem guarded_application {term : Trm TrmVar} {tIn tOut : Lp2lc.Active.STLC.Typ}
    (typing : Typ.AsSemantic (TrmVar := TrmVar) (tIn :=> tOut) term) :
    ∀ steps : Nat, ∀ smaller : Nat, smaller < steps ->
      ∀ argument : Trm TrmVar, Safe (TrmVar := TrmVar) smaller argument tIn ->
        Later (Safe (TrmVar := TrmVar) smaller (.apply term argument) tOut) := by
  intro steps
  cases steps with
  | zero =>
      intro smaller smaller_lt
      cases Nat.not_lt_zero _ smaller_lt
  | succ steps =>
      intro smaller smaller_lt argument argument_safe
      have safeFunction : Safe (TrmVar := TrmVar) (steps + 1) term (tIn :=> tOut) :=
        fundamental_lemma (TrmVar := TrmVar) typing (steps + 1)
      unfold Safe at safeFunction
      exact safeFunction.2 smaller smaller_lt argument argument_safe

theorem soundness {term : Trm TrmVar} {type : Lp2lc.Active.STLC.Typ}
    (typing : Typ.AsSemantic (TrmVar := TrmVar) type term) :
    Typ.AsSemantic (TrmVar := TrmVar) type term := by
  have _ := fundamental_lemma (TrmVar := TrmVar) typing
  exact typing

end Semantic

end PHOAS


end STLC
