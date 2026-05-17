package DTLC.Example

import Tests.Preamble

object TrmSpec extends Preamble {

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
}
