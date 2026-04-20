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
     DOT only contains structural typing
     */

    val structural1Trm: { val a: Boolean } = { // object with 1 term entry
      val a = false
    }

    val structural1Typ: { type A } = { // object with 1 type alias entry
      type A
    }

    // so trait & type bound in Scala requires some elaboration:
    trait EmptyTrait {}
    // becomes:
    { type Tag = this.type }

    trait SubTrait extends EmptyTrait {}
    // becomes
    { type Tag = this.type; given Tag <:< EmptyTrait }

    trait T1 { type A }
    val trait0: T1 = { // object with 1 type a
      new T1
    }
  }

}
