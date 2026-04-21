package DOT

object SanityExample extends Preamble {

  object Trm {
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

    /*
     structural type and trait/class definition largely follows step-indexed gDOT convention
     namely trait is elaborated into a structural type with class tag
     */
    val structural1Trm: { val a: Boolean } = {
      val a = false
    } // 1 term entry in a self-binder

    val structural1Typ: { type A } = {
      type A
    } // 1 type alias entry in a self-binder

    trait EmptyTrait {} // elaborated into: { type class_EmptyTrait }

    /*
     the only change on top of gDOT is that type bounds are
     now elaborated into nameless implicit evidence entry (subtypeEv)
     */

    val structural1Bounded: {
      type A >: Nothing <: EmptyTrait
    } = {} // elaborated into { type A ; given Nothing <:< A ; given A <:< EmptyTrait}

  }

}
