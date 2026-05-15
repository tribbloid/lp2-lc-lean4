package DOT.Example

import Tests.Preamble

object SanityExample extends Preamble {

  object TypAndTrm {
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
     structural type and trait/class definition largely follows
     step-indexed gDOT ("Scala step-by-step: soundness for DOT with step-indexed logical relations in Iris") convention
     namely, each trait is elaborated into a structural type with class tag
     */
    val structural1Trm: { val a: Boolean } = {
      new AnyRef { val a = false }
    }

    val structural1Typ: { type A } = {
      new AnyRef { type A }
    } // 1 type alias entry in a self-binder

    trait EmptyTrait {} // elaborated into: { type class_EmptyTrait }

    /*
     the only change on top of gDOT is that type bounds are
     now elaborated into nameless implicit evidence entry (subtypeEv)
     */

    val structural1Bounded: {
      type A >: Nothing <: EmptyTrait
    } = new AnyRef {
      type A >: Nothing <: EmptyTrait
    } // elaborated into { type A ; given Nothing <:< A ; given A <:< EmptyTrait}

    trait SubTrait
        extends EmptyTrait // elaborated into: { type class_EmptyTrait ; type class_SubTrait; given class_SubTrait <:< class_EmptyTrait }
  }

  {
    def f(x: Int): Int = ???
    def g(x: Int): Int = ???
    def h(x: Int): Int = ???

    // primary
    {
      val x = f.apply(1) + 1
      val y = g.apply(x) + 1
      h.apply(y) + 1
    }

    // dual, Gentzen's sequent form:
    {
      { (y: Int) =>
        h.apply(y) + 1
      }.apply {
        { (x: Int) =>
          g.apply(x) + 1
        }.apply(f.apply(1) + 1)
      }
    }
  }

}
