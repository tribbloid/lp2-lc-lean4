package Example

import Example.Preamble

/**
  * Scala counterparts of the shared fixtures in Tests/STLC/TrmDemo.lean, Tests/STLC_minimal/TrmDemo.lean,
  * Tests/DTLC/TrmDemo.lean, and Tests/DSub/TrmDemo.lean.
  *
  * Shared terms and type hints must stay consistent with those Lean demos. InDSub.Undecidable contains Scala-only
  * examples whose Lean counterparts are deferred.
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
      /* DONE: Add Scala examples illustrating undecidable subtyping.

        Use the bounded-quantification encoding in Hu and Lhotak, Sections 4.2-4.7:
          https://plg.uwaterloo.ca/~olhotak/pubs/1908.05294.pdf
        and the cyclic-subtyping example in Mackay et al., Section 3.4:
          https://www.cs.cmu.edu/~aldrich/papers/popl20-decidable-DOT.pdf
        Ghelli's nonterminating query is reproduced by Pierce in Section 6.2.3:
          https://www.cs.cmu.edu/~rwh/students/pierce.pdf

        Finite examples illustrate the mechanisms; the papers supply the undecidability proofs.
        Recursive Wyvern examples go beyond DSub and must be identified as such.
        Compiler rejection is acceptable; it does not itself prove undecidability.
        Lean demo counterparts are deferred and must not be added in this task.
       */

      import scala.compiletime.testing.typeChecks

      // Bounded quantification selects x.Type from a structural member, as in Hu and Lhotak's encoding.
      type Negate[T] = (x: { type Type <: T }) => x.Type

      // Scala accepts an explicit adapter but rejects the direct dependent-function subtype comparison below.
      def narrowNegation1: Negate[Any] => Negate[Boolean] =
        value => { x => value(x) }

      def narrowNegation2(value: Negate[Any]): Negate[Boolean] = { x => value(x) }

// [error] 216 |      def narrow(value: Negate[Any]): Negate[Boolean] = value
// [error]     |                                                        ^^^^^
// [error]     |    Found:    (value : Example.TrmDemo.InDSub.Undecidable.Negate[Any])
// [error]     |    Required: Example.TrmDemo.InDSub.Undecidable.Negate[Boolean]
      def narrowAccepted: false = typeChecks("""
      def narrow(value: Negate[Any]): Negate[Boolean] = value
      """)

      // Ghelli's finite bound contains nested quantification and contravariant occurrences of selected types.
      type ExpandingBound = (x: { type Type }) => Negate[(y: { type Type <: x.Type }) => Negate[y.Type]]

      // Full F<: subtype search repeats the query with x1.Type in place of x0.Type, under x1.Type <: x0.Type,
      // adding another binding each time. Scala 3.10.0 instead reports a type mismatch for this translation.
      val expandingSubtypingAccepted: false = typeChecks("""
      def expandingSubtyping(x0: { type Type <: ExpandingBound })(value: x0.Type): (x1: {
        type Type <: x0.Type
      }) => Negate[x1.Type] = value
      """)

      // Mackay et al., Section 3.4: direct self-reference, beyond DSub's nonrecursive objects.
      // Scala 3.10.0 detects the illegal cyclic upper bound; this is distinct from Ghelli's growing context.
      val cyclicBoundAccepted: false = typeChecks("""
        object cyclic {
          type Type <: cyclic.Type
        }
      """)
    }
  }
}
