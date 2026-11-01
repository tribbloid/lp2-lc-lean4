package Example

import Example.Preamble

object TypDemo extends Preamble {

  type `false` = Boolean

  type tFalse = `false`

  type idFn = Boolean => Boolean

  type get1st = Boolean => Boolean => Boolean

  type apply1stOn2ndFn = (Boolean => Boolean) => Boolean => Boolean

  object InDSub {

    type boolType = { type Type = Boolean }

    type fnType = { type Type = idFn }

    type boundedMember = { type Type >: Nothing <: Boolean }

    type lowerBoundedMember = { type Type >: Boolean }

    type abstractMember = { type Type }

    type dependentId = (x: abstractMember) => x.Type => x.Type

    type dependentType = (x: abstractMember) => { type Type = x.Type }

    type capturedId = (x: abstractMember) => abstractMember => x.Type => x.Type

    type boundedDependentId = (x: boundedMember) => x.Type => Boolean

    type selectedBool = TrmDemo.InDSub.boolType.Type

    type selectedFn = TrmDemo.InDSub.fnType.Type
  }
}
