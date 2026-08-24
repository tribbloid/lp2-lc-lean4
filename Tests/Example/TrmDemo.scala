package Example

import Example.Preamble

/**
  * All definitions in [[../**/**Demo.lean]] must be consistent with the following example in Scala (the
  * object-language).
  *
  * both terms and type hints should be consistent
  */
object TrmDemo extends Preamble {

  type Primitive = Boolean

  val vFalse: Boolean = false

  val vTrue: Boolean = true

  val idFn: (v: Any) => v.type = // doesn't exist in STLC,
    x => x

  val primitiveIdFn: Boolean => Boolean =
    x => x

  val idFnOnFalse: Boolean =
    idFn(vFalse)

  val primitiveIdFnOnFalse: Boolean =
    primitiveIdFn(vFalse)

  val get1st: Boolean => Boolean => Boolean =
    x => _y => x

  val get2nd: Boolean => Boolean => Boolean =
    _x => y => y

  val get1stOnTuple: Boolean =
    get1st(vFalse)(vTrue)

  val get2ndOnTuple: Boolean =
    get2nd(vFalse)(vTrue)

  val apply1stOn2ndFn: ((v: Any) => v.type) => Boolean => Boolean =
    f => x => f(x)

  val apply1stOn2ndFnOnTuple: Boolean =
    apply1stOn2ndFn(idFn)(vFalse)

  val applyidFnOnItself =
    idFn(idFn)

  val idFnOnFalse2: Boolean =
    applyidFnOnItself(vFalse)

  val primitiveTrueFn: Boolean => Boolean =
    _ => true

  val primitiveTrueFnOnFalse: Boolean =
    primitiveTrueFn(vFalse)

  object TypeHinted {

    val hintedFalse: Boolean =
      false

    val hintedIdFn: Boolean => Boolean = { x => x }

    val hintedIdFnOnFalse: Boolean =
      hintedIdFn(hintedFalse)
  }

  object Malformed {

    lazy val primitiveApply: Boolean =
      vFalse.asInstanceOf[Boolean => Boolean](vTrue)

    lazy val apply1: Boolean =
      idFn(vFalse).asInstanceOf[Boolean => Boolean](vTrue)

    lazy val primitiveFalseAsFn: Boolean => Boolean =
      vFalse.asInstanceOf[Boolean => Boolean]

    lazy val idFnAsPrimitive: Boolean =
      idFn.asInstanceOf[Boolean]

    lazy val binderIdentityCounterexample: Boolean = {
      val fn: Boolean => Boolean => Boolean =
        outer => inner =>
          if (inner == outer)
            inner
          else
            vFalse.asInstanceOf[Boolean => Boolean](vTrue)
      fn(vFalse)(vTrue)
    }
  }
}
