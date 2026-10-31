package Example

import Example.Preamble

/**
  * Scala counterparts of the shared fixtures in Tests/STLC/TrmDemo.lean, Tests/STLC_minimal/TrmDemo.lean,
  * Tests/DTLC/TrmDemo.lean, and Tests/DSub/TrmDemo.lean.
  *
  * Both terms and type hints must stay consistent with those Lean demos.
  */
object TrmDemo extends Preamble {

  type Primitive = Boolean

  val vFalse: Boolean = false

  val vTrue: Boolean = true

  val primitiveIdFn: Boolean => Boolean =
    x => x

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

  val primitiveTrueFn: Boolean => Boolean =
    _ => true

  val primitiveTrueFnOnFalse: Boolean =
    primitiveTrueFn(vFalse)

  val get1stOnFalse: Boolean => Boolean =
    get1st(vFalse)

  val higherOrderId: (Boolean => Boolean) => Boolean => Boolean =
    f => f

  val higherOrderApplication: Boolean =
    higherOrderId(primitiveIdFn)(vFalse)

  // Native Scala callbacks represent fnPrimitive; ordinary lambdas above represent fn.
  val primitiveLiteralIdFn: Boolean => Boolean =
    identity[Boolean]

  val primitiveLiteralIdFnOnFalse: Boolean =
    primitiveLiteralIdFn(vFalse)

  val primitiveFirstFnOnTuple: Boolean = {
    val primitive: Boolean => Boolean => Boolean = get1st
    primitive(vFalse)(vTrue)
  }

  object Malformed {

    lazy val WrongTIn: Boolean =
      primitiveIdFn(primitiveIdFn.asInstanceOf[Boolean])

    lazy val ContainWrongTIn: Boolean =
      WrongTIn.asInstanceOf[Boolean => Boolean](vFalse)

    lazy val applyLit1: Boolean =
      vFalse.asInstanceOf[Boolean => Boolean](vTrue)

    lazy val applyLit2: Boolean =
      primitiveIdFn(vFalse).asInstanceOf[Boolean => Boolean](vTrue)

    lazy val applyLitToApplication: Boolean =
      vFalse.asInstanceOf[Boolean => Boolean](primitiveIdFnOnFalse)

    lazy val wrongNestedTIn: Boolean => Boolean =
      higherOrderId(get1st.asInstanceOf[Boolean => Boolean])

    lazy val primitiveLiteralIdFnOnFn: Boolean =
      primitiveLiteralIdFn(primitiveIdFn.asInstanceOf[Boolean])
  }

  // Casts expose the primitive callbacks' broken result contracts; all failures stay lazy.
  object Corrupted {

    lazy val corruptApplication: Boolean => Boolean = {
      val primitive: Boolean => (Boolean => Boolean) =
        x => x.asInstanceOf[Boolean => Boolean]
      primitive(vFalse)
    }

    lazy val corruptedCallee: Boolean =
      corruptApplication(vTrue)

    lazy val corruptedArgument: Boolean => Boolean =
      higherOrderId(corruptApplication)

    lazy val corruptedBody: Boolean => Boolean = {
      val fn: Boolean => (Boolean => Boolean) = _ => corruptApplication
      fn(vFalse)
    }

    lazy val illTypedPrimitiveResult: Boolean = {
      val primitive: Boolean => Boolean = _ => {
        val result: Boolean => Boolean =
          _ => "bad".asInstanceOf[String => Boolean]("bad")
        result.asInstanceOf[Boolean]
      }
      primitive(vFalse)
    }

    lazy val primitiveFnOnTuple: Boolean = {
      val primitive: Boolean => Boolean => Boolean =
        _ => _ => ValDemo.idFn.asInstanceOf[Boolean]
      primitive(vFalse)(vTrue)
    }
  }
}
