package Example

import Example.Preamble

object ValDemo extends Preamble {

  val vFalse: Boolean = TrmDemo.vFalse

  val vTrue: Boolean = TrmDemo.vTrue

  val idFn: Boolean => Boolean =
    x => x
}
