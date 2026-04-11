import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC

namespace Trm

-- AKA intermediate representation (IR): reify the term in Lean.
-- map `_self` to a compatible lean type, e.g. Trm.function should be mapped to an actual lean function type
def Denotation (_self : Trm TrmVar) : Type := Trm TrmVar

-- AKA intermediate representation (IR): reify the term in Lean.
def denotation : (self : Trm TrmVar) -> self.Denotation :=
  fun self =>
    match self with
    | .var name declared => .var name declared
    | .literal instructions declared => .literal instructions declared
    | .function body => .function body
    | .apply fn arg => .apply (denotation fn) (denotation arg)

end Trm

namespace Sanity

-- contains verified examples and test cases of things in Def

-- All docstrings use short (under 5 lines) of Scala code as demonstrations.

abbrev base_variable : Trm Unit :=
  Trm.var () .base

abbrev arrow_variable : Trm Unit :=
  Trm.var () (.base :=> .base)

abbrev one_argument_base_function : Trm Unit :=
  Trm.function (fun argument => .var argument .base)

abbrev applies_to_base_variable : Trm Unit :=
  Trm.apply one_argument_base_function base_variable

abbrev applies_to_arrow_variable : Trm Unit :=
  Trm.apply one_argument_base_function arrow_variable

abbrev invalid_application : Trm Unit :=
  Trm.apply base_variable base_variable

example : Typ.base.AsSemantic (TrmVar := Unit) base_variable = True := by
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    simpa [base_variable] using
      (Typ.AsSemantic.var (name := ()) (declared := Typ.base))

example : Typ.base.AsSemantic (TrmVar := Unit) applies_to_base_variable = True := by
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    unfold applies_to_base_variable one_argument_base_function base_variable
    refine Typ.AsSemantic.apply (tIn := Typ.base) ?_ ?_
    · refine Typ.AsSemantic.function ?_
      intro argument
      exact Typ.AsSemantic.var
    · exact Typ.AsSemantic.var

example : Typ.base.AsSemantic (TrmVar := Unit) applies_to_arrow_variable = True := by
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    unfold applies_to_arrow_variable one_argument_base_function arrow_variable
    refine Typ.AsSemantic.apply (tIn := Typ.base :=> Typ.base) ?_ ?_
    · refine Typ.AsSemantic.function ?_
      intro argument
      exact Typ.AsSemantic.var
    · exact Typ.AsSemantic.var

example : Typ.base.AsSemantic (TrmVar := Unit) one_argument_base_function = False := by
  apply propext
  constructor
  · intro typing
    unfold one_argument_base_function at typing
    cases typing
  · intro falsehood
    cases falsehood

example : Typ.base.AsSemantic (TrmVar := Unit) invalid_application = False := by
  apply propext
  constructor
  · intro typing
    unfold invalid_application base_variable at typing
    cases typing with
    | apply function_typing _ =>
        cases function_typing
  · intro falsehood
    cases falsehood


end Sanity
