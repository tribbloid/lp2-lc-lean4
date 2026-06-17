package DTLC.Example

import Tests.Preamble

object TypDemo extends Preamble {

  type `false` = Boolean

  type idFn = Boolean => Boolean

  type get1st = Boolean => Boolean => Boolean

  type apply1stOn2ndFn = (Boolean => Boolean) => Boolean => Boolean
}
