import «Lp2lc».Active.DTLC.Runtime
import Tests.DTLC.Sanity

namespace Tests.DTLC.RuntimeCheck

open Lp2lc.Active.DTLC

variable {I : Index} [Tests.DTLC.Sanity.FIso I]

attribute [local simp] Runtime.compile Runtime.Compiled.run Runtime.Compiled.apply
attribute [local simp] Runtime.SemanticVal.to_val
attribute [local simp] Tests.DTLC.Sanity.Trm.false Tests.DTLC.Sanity.Trm.true
attribute [local simp] Tests.DTLC.Sanity.Trm.idFn Tests.DTLC.Sanity.Trm.idFnOnFalse
attribute [local simp] Tests.DTLC.Sanity.Trm.applyidFnOnItself
attribute [local simp] Tests.DTLC.Sanity.Trm.malformedPrimitiveApply
attribute [local simp] Tests.DTLC.Sanity.Typ.false Tests.DTLC.Sanity.Typ.idFn

example :
    Runtime.compile (I := I) (trm := (Tests.DTLC.Sanity.Trm.false : Trm I)) (fuel := 0)
      (type_annotation := (Tests.DTLC.Sanity.Typ.false : Typ I)) = .out_of_fuel := rfl

example :
    Runtime.compile (I := I) (trm := (Tests.DTLC.Sanity.Trm.false : Trm I)) (fuel := 1)
      (type_annotation := (Tests.DTLC.Sanity.Typ.false : Typ I)) =
        .success
          ({ type_annotation := (Tests.DTLC.Sanity.Typ.false : Typ I),
              value := .primitive "false" } :
            Runtime.Compiled I) := rfl

example :
    Runtime.compile (I := I) (trm := (Tests.DTLC.Sanity.Trm.false : Trm I)) (fuel := 1)
      (type_annotation := (.top : Typ I)) =
        .success
          ({ type_annotation := (.top : Typ I), value := .primitive "false" } :
            Runtime.Compiled I) := rfl

example :
    Runtime.compile (I := I) (trm := (Tests.DTLC.Sanity.Trm.idFn : Trm I)) (fuel := 1)
      (type_annotation := (Tests.DTLC.Sanity.Typ.idFn : Typ I)) =
        .success
          ({ type_annotation := (Tests.DTLC.Sanity.Typ.idFn : Typ I),
              value := .fn (body := fun x => Tests.DTLC.Sanity.FIso.rev x) } :
            Runtime.Compiled I) := rfl

example :
    Runtime.compile (I := I) (trm := (Tests.DTLC.Sanity.Trm.idFn : Trm I)) (fuel := 1)
      (type_annotation := (.top : Typ I)) =
        .success
          ({ type_annotation := (.top : Typ I),
              value := .fn (body := fun x => Tests.DTLC.Sanity.FIso.rev x) } :
            Runtime.Compiled I) := rfl

example :
    Runtime.Compiled.run
      ({ type_annotation := (.top : Typ I), value := .primitive "false" } : Runtime.Compiled I)
      0 = .out_of_fuel := rfl

example :
    Runtime.Compiled.run
      ({ type_annotation := (.top : Typ I), value := .primitive "false" } : Runtime.Compiled I)
      1 = .success (.primitive "false") := rfl

example :
    Runtime.Compiled.apply
      ({ type_annotation := (.top : Typ I),
          value := .fn (body := fun x => Tests.DTLC.Sanity.FIso.rev x) } : Runtime.Compiled I)
      ({ type_annotation := (.top : Typ I), value := .primitive "false" } : Runtime.Compiled I)
      2
      (Tests.DTLC.Sanity.Typ.false : Typ I) =
        .success
          ({ type_annotation := (Tests.DTLC.Sanity.Typ.false : Typ I),
              value := .primitive "false" } :
            Runtime.Compiled I) := by
  simp

example :
    Runtime.Compiled.apply
      ({ type_annotation := (.top : Typ I),
          value := .fn (body := fun x => Tests.DTLC.Sanity.FIso.rev x) } : Runtime.Compiled I)
      ({ type_annotation := (.top : Typ I),
          value := .fn (body := fun x => Tests.DTLC.Sanity.FIso.rev x) } : Runtime.Compiled I)
      2
      (.top : Typ I) =
        .success
          ({ type_annotation := (.top : Typ I),
              value := .fn (body := fun x => Tests.DTLC.Sanity.FIso.rev x) } :
            Runtime.Compiled I) := by
  simp

example :
    Runtime.Compiled.apply
      ({ type_annotation := (Tests.DTLC.Sanity.Typ.idFn : Typ I),
          value := .fn (body := fun x => Tests.DTLC.Sanity.FIso.rev x) } : Runtime.Compiled I)
      ({ type_annotation := (.top : Typ I),
          value := .fn (body := fun x => Tests.DTLC.Sanity.FIso.rev x) } : Runtime.Compiled I)
      2
      (.top : Typ I) = .type_error := rfl

example :
    Runtime.compile (I := I) (trm := (Tests.DTLC.Sanity.Trm.idFnOnFalse : Trm I)) (fuel := 3)
      (type_annotation := (Tests.DTLC.Sanity.Typ.false : Typ I)) =
        .success
          ({ type_annotation := (Tests.DTLC.Sanity.Typ.false : Typ I),
              value := .primitive "false" } :
            Runtime.Compiled I) := by
  simp

example :
    Runtime.compile (I := I) (trm := (Tests.DTLC.Sanity.Trm.malformedPrimitiveApply : Trm I))
      (fuel := 1) (type_annotation := (Tests.DTLC.Sanity.Typ.false : Typ I)) =
        .out_of_fuel := rfl

example :
    Runtime.compile (I := I) (trm := (Tests.DTLC.Sanity.Trm.malformedPrimitiveApply : Trm I))
      (fuel := 2) (type_annotation := (Tests.DTLC.Sanity.Typ.false : Typ I)) =
        .type_error := rfl

end Tests.DTLC.RuntimeCheck
