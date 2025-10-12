package lp2lc

import scala.compiletime.ops.int.+

// scope section
object Rosetta {

  // nameless scope section
  {
    // define things
  }

  {
    // type
    type T1 = String

    // proposition
    type P1 = 2 + 2 =:= 4

    // instance / inhabitant / example
    lazy val v1: T1 = "hello"
    //    def v2: T1 = "hello" TODO: this is impure, equivalent to an IO monad in Lean4

    // proving automatically
    val p1: P1 = implicitly[P1]

    {
      // type definition pending or left as an exercise
      type T

      // inhabitant / example pending or left as an exercise
      val v: T = ???
    }
  }

  // constructive
  // no complement
  // no law of excluded middle
  {

    // system lambda / simply-typed lambda calculus
    // propositional logic
    {
      type A
      type B

      // function / lambda
      // if v satisfy A, then fn(v) satisfy B
      {
        inline def fn1(inline v: A): B = ???

        val fn2: A => B = v => ???
        val fn3: A => B = ???
      }

      // product type
      // if a and b satisfy A and B respectively, then fn(a, b) satisfy C
      {
        type C1

        def fn1(a_b: (A, B)): C1 = ???

        case class C2(a: A, b: B)
      }

      // sum/inductive type
      // if v satisfy A or B, then fn1(v) or fn2(v) satisfy C
      {
        type C1

        def fn1(v: A | B): C1 = ???

        object C1 {
          implicit def fn1: A => C1 = ???
          implicit def fn2: B => C1 = ???
        }

        sealed trait C2
        object C2 {
          case class fn1(a: A) extends C2
          case class fn2(b: B) extends C2
        }

        // infinite / structural
        {
          object zero

          case class succeed(v: Nat1)

          type Nat1 = zero.type | succeed

          sealed trait Nat2

          object Nat2 {
            case object zero extends Nat2
            case class succeed(n: Nat2) extends Nat2
          }
        }
      }
    }

    // system lambdaP
    // predicative logic
    object DependentTypes {

      // dependent type
      // B that depends on an example of A
      trait A1 {
        type D
      }

      type A2

      implicit class A2View(a: A2) {
        type D
      }

      type B

      // dependent Pi type
      // universal quantifier
      // for all v that satisfy A, fn(v) always satisfy D(v)
      {
        def fn1(v: A1): v.D = ???

        def fn2[T <: A1](v: T): v.D = ???

        val fn3: (v: A1) => v.type = ???
      }

      // dependent Sigma type
      // existential quantifier
      // if v satisfy A, at least one v2 can be found to satisfy D(v), such that fn(v)(v2) satisfy B
      {
        def fn1(v: A1)(v2: v.D): B = ???

        def fn2(v: A1): v.D => B = ???

        val fn3: (v: A1) => v.D => B = ???
      }
    }

    // system lambda2 / F
    // 2nd order propositional logic
    object Polymorphs {

      type B

      trait TypeCls {
        type For

        def get: B
      }

      // parametric
      // for all A that can be satisfied / for the whole collection that satisfy A
      //  ... B has a constructive proof fn(A)
      {
        def fn1[T]: B = ???

        object TypeCls {
          class Evidence[A] extends TypeCls {
            type For = A
            lazy val get: B = ???
          }
          implicit def _1[A]: Evidence[A] = new Evidence[A]
        }

        def fn2[T](
            implicit
            evidence: TypeCls { type For = T }
        ): B = evidence.get
      }

      // ad-hoc
      // for all A that can be satisfied and can be covered by several cases / for several collections that constitutes A
      //  ... each one has a different constructive proof for B
      {
        type A1
        type A2

        object TypeCls {
          implicit object _1 extends TypeCls {
            type For = A1
            lazy val get: B = ???
          }
          implicit object _2 extends TypeCls {
            type For = A2
            lazy val get: B = ???
          }
        }

        def fn1[T](
            implicit
            evidence: TypeCls { type For = T }
        ): B = evidence.get
      }
    }

    // system lambdaC / calculus of constructions
    object HigherKinds {}
  }
}
