package DTLC.Example

import Tests.Preamble

/**
  * Everything here should have a [[../TrmDemo.lean]] counterpart
  */
object TrmDemo extends Preamble {

  val `false`: Boolean = false

  val `true`: Boolean = true

  val idFn: (v: Boolean) => v.type =
    x => x

  val idFnOnFalse: Boolean =
    idFn(`false`)

  val get1st: Boolean => Boolean => Boolean =
    x => _y => x

  val get2nd: Boolean => Boolean => Boolean =
    _x => y => y

  val get1stOnTuple: Boolean =
    get1st(`false`)(`true`)

  val get2ndOnTuple: Boolean =
    get2nd(`false`)(`true`)

  val apply1stOn2ndFn: (Boolean => Boolean) => Boolean => Boolean =
    f => x => f(x)

  val apply1stOn2ndFnOnTuple: Boolean =
    apply1stOn2ndFn(idFn)(`false`)

  val applyidFnOnItself: Boolean => Boolean =
    ((f: Boolean => Boolean) => f)((x: Boolean) => x)

  val idFnOnFalse2: Boolean =
    applyidFnOnItself(`false`)

  val primitiveTrueFn: Boolean => Boolean =
    _ => true

  val primitiveTrueFnOnFalse: Boolean =
    primitiveTrueFn(`false`)

  object TypeHinted {

    val hintedFalse: Boolean =
      false

    val hintedIdFn: Boolean => Boolean = { x => x }

    val hintedIdFnOnFalse: Boolean =
      hintedIdFn(hintedFalse)
  }

  object Malformed {

    lazy val primitiveApply: Boolean =
      `false`.asInstanceOf[Boolean => Boolean](`true`)

    lazy val apply1: Boolean =
      idFn(`false`).asInstanceOf[Boolean => Boolean](`true`)

    lazy val primitiveFalseAsFn: Boolean => Boolean =
      `false`.asInstanceOf[Boolean => Boolean]

    lazy val idFnAsPrimitive: Boolean =
      idFn.asInstanceOf[Boolean]
  }
}
