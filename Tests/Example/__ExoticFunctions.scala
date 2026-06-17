package Example

import scala.compiletime.constValue
import scala.compiletime.ops.int.*

object __ExoticFunctions {

  def v3: 3 = 3
  inline def v4: 4 = 4

  // CAUTION: implicit summoning is strictly forbidden here

  val _ = {
    // type `N + 3` is special type not in DOT, it can only be summoned but not inferred
    // it should be a full dependent type depending on a deterministic term

    // transparent inline def plus3[N <: Int & Singleton](inline v: N): N + 3 = v + 3
  }

  // val _ = {
  //   inline def plus3[N <: Int & Singleton](inline v: N): N + 3 = v + 3

  //   def five = plus3(2) // eval in runtime
  //   def six = plus3(v3) // inline function can use value that is Singleton but not inlined
  //   def seven = plus3(v4)
  // }

  // val _ = {

  //   // ditto theoretically, dependent type can depends on inlined/cached expression
  //   inline def plus3(v: Int & Singleton): v.type + 3 = v + 3

  //   def five: 5 = plus3(2)
  //   def six: 6 = plus3(v3) // "error: (v$proxy2 : Int) + (3 : Int) is not a constant type;" this is wrong
  //   def seven = plus3(v4)
  // }

  // val _ = {
  //   // doesn't work, non-inline function can change type-checking behaviour
  //   def plus3[N <: Int & Singleton](v: N): N + 3 = v + 3
  // }

}
