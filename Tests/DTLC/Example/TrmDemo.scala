package DTLC.Example

import Tests.Preamble

object TrmDemo extends Preamble {

  val `false`: Boolean = false

  val `true`: Boolean = true

  val identityFn: Boolean => Boolean =
    x => x

  val identityFnOnFalse: Boolean =
    identityFn(`false`)

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
    apply1stOn2ndFn(identityFn)(`false`)

  val applyidFnOnItself: Boolean => Boolean =
    ((f: Boolean => Boolean) => f)((x: Boolean) => x)

  val idFnOnFalse2: Boolean =
    applyidFnOnItself(`false`)

  val primitiveTrueFn: Boolean => Boolean =
    _ => true

  val primitiveTrueFnOnFalse: Boolean =
    primitiveTrueFn(`false`)

  val annotatedFalse: Boolean =
    false

  val annotatedIdFn: Boolean => Boolean =
    (x: Boolean) => x

  val annotatedIdFnOnFalse: Boolean =
    annotatedIdFn(annotatedFalse)

  object Malformed {

    lazy val primitiveApply: Boolean =
      `false`.asInstanceOf[Boolean => Boolean](`true`)

    lazy val apply1: Boolean =
      identityFn(`false`).asInstanceOf[Boolean => Boolean](`true`)
  }
}
