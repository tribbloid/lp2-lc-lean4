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

  object InDSub {
    /* DONE: Add examples of DSub syntax (TMember, TSel, and typeDef) here.

      Use structural types with a single member named `Type` instead of nominal Scala classes.

      Recommended workflow:
        - Add Scala examples.
        - Add matching Lean namespaces and examples in Tests/DSub/TrmDemo.lean and TypDemo.lean.
        - Test `Trm.infer` and `Trm.eval_certified` from Serial/__Eval_certifiedByInfer.lean
          against Scala compiler behaviour; let mismatches fail the Lean checks.
        - Once finished, change this issue's prefix from "TODO" to "DONE".
     */

    val boolType: TypDemo.InDSub.boolType = new { type Type = Boolean }

    val fnType: TypDemo.InDSub.fnType = new { type Type = Boolean => Boolean }

    val boundedId: TypDemo.InDSub.boundedMember => TypDemo.InDSub.boundedMember =
      x => x

    val boundedApplication: TypDemo.InDSub.boundedMember =
      boundedId(boolType)

    val selectedId: TypDemo.InDSub.selectedBool => TypDemo.InDSub.selectedBool =
      x => x

    val selectedApplication: TypDemo.InDSub.selectedBool =
      selectedId(vFalse)

    val selectedFnId: TypDemo.InDSub.selectedFn => TypDemo.InDSub.selectedFn =
      f => f

    val selectedFnApplication: TypDemo.InDSub.selectedBool =
      selectedFnId(primitiveIdFn)(vTrue)

    object Malformed {

      private inline def checkTyping(inline code: String, inline expected: Boolean): Unit =
        inline if scala.compiletime.testing.typeChecks(code) != expected then
          scala.compiletime.error("The DSub example has an unexpected type-checking result.")

      checkTyping("boundedId(boolType); selectedId(vFalse); selectedFnId(primitiveIdFn)", true)

      lazy val applyTypeDef: Boolean =
        boolType.asInstanceOf[Boolean => Boolean](vFalse)

      checkTyping("boolType(vFalse)", false)

      lazy val wrongMember: TypDemo.InDSub.boundedMember =
        boundedId(new { type Type = Any }.asInstanceOf[TypDemo.InDSub.boundedMember])

      checkTyping("boundedId(new { type Type = Any })", false)

      lazy val wrongSelectedArgument: TypDemo.InDSub.selectedBool =
        selectedId(boolType.asInstanceOf[TypDemo.InDSub.selectedBool])

      checkTyping("selectedId(boolType)", false)

      lazy val wrongSelectedFnArgument: TypDemo.InDSub.selectedFn =
        selectedFnId(vFalse.asInstanceOf[TypDemo.InDSub.selectedFn])

      checkTyping("selectedFnId(vFalse)", false)
    }

    object Undecidable {
      /* TODO: System DSub is undecidable

      as shown in articles:
        - Undecidability of D<: and Its Decidable Fragments
        - Decidable Subtyping for Path Dependent Types

      the examples that shows undecidability should be added here, breaking compilation is acceptable

      The Lean Demo counterparts don't need to be added and will be added later.
       */

    }
  }
}
