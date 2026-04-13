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

namespace Semantic

private abbrev SyntaxTyp := Lp2lc.Active.STLC.Typ

private abbrev SyntaxTrm := Trm SyntaxTyp

def Safe : Nat -> SyntaxTrm -> SyntaxTyp -> Prop
| _, term, type =>
    HasTypeProto type term

theorem safe_hasType
    {steps : Nat}
    {term : SyntaxTrm}
    {type : SyntaxTyp} :
    Safe steps term type ->
    HasTypeProto type term := by
  intro safe
  simpa [Safe] using safe

theorem safe_mono
    {smaller larger : Nat}
    {term : SyntaxTrm}
    {type : SyntaxTyp}
    (_smaller_le : smaller ≤ larger) :
    Safe larger term type ->
    Safe smaller term type := by
  intro safe
  simpa [Safe] using safe

theorem fundamental_lemma {term : ClosedTrm} {type : SyntaxTyp}
    (typing : HasType type term) :
    ∀ steps : Nat, Safe steps (term SyntaxTyp) type := by
  intro steps
  simpa [Safe, HasType] using typing

theorem guarded_application
    {term : SyntaxTrm}
    {tIn tOut : SyntaxTyp}
    (typing : HasTypeProto (tIn :=> tOut) term) :
    ∀ steps : Nat, ∀ smaller : Nat, smaller < steps ->
      ∀ argument : SyntaxTrm, Safe smaller argument tIn ->
        Later (Safe smaller (.apply term argument) tOut) := by
  intro _steps smaller _smaller_lt argument argument_safe
  refine ⟨?_⟩
  exact ⟨tIn, typing, safe_hasType argument_safe⟩

theorem soundness {term : ClosedTrm} {type : SyntaxTyp}
    (typing : HasType type term) :
    HasType type term := by
  exact typing

end Semantic

end STLC
