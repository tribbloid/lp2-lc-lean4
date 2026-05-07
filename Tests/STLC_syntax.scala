/**
  * using simple HOAS (higher-order abstract syntax) convention
  *
  * any syntax & normalize defintion longer than this is heresy
  */
object STLC_syntax {

  sealed trait Trm[A]

  sealed trait Val[A] extends Trm[A]

  object Trm {
    final case class Literal[A](code: String) extends Val[A]
    final case class Lam[A, B](body: Val[A] => Trm[B]) extends Val[A => B]
    final case class App[A, B](fn: Trm[A => B], arg: Trm[A]) extends Trm[B]

    def literal[A](code: String): Val[A] =
      Literal(code)

    def lam[A, B](body: Val[A] => Trm[B]): Val[A => B] =
      Lam(body)

    def app[A, B](fn: Trm[A => B], arg: Trm[A]): Trm[B] =
      App(fn, arg)

    def normalize[A](trm: Trm[A]): Val[A] =
      trm match {
        case literal: Literal[a] =>
          literal
        case lam: Lam[a, b] =>
          Lam[a, b](x => normalize(lam.body(x)))
        case App(fn, arg) =>
          val arg1 = normalize(arg)
          normalize(fn) match {
            case Lam(body) =>
              normalize(body(arg1))
            case others =>
              throw new RuntimeException(s"malformed application: $fn is not a Lambda & cannot be applied")
          }
      }
  }

  object Examples {
    import Trm.*

    val `false`: Val[Boolean] =
      literal("false")

    val `true`: Val[Boolean] =
      literal("true")

    val ifThenElse: Val[Boolean => Boolean => Boolean => Boolean] =
      literal("if")

    val identityFn: Val[Boolean => Boolean] =
      lam[Boolean, Boolean](x => x)

    val identityFnOnFalse: Trm[Boolean] =
      app(identityFn, `false`)

    val get1st: Val[Boolean => Boolean => Boolean] =
      lam[Boolean, Boolean => Boolean](x => lam[Boolean, Boolean](_ => x))

    val get2nd: Val[Boolean => Boolean => Boolean] =
      lam[Boolean, Boolean => Boolean](_ => lam[Boolean, Boolean](y => y))

    val get1stOnTuple: Trm[Boolean] =
      app(app(get1st, `false`), `true`)

    val get2ndOnTuple: Trm[Boolean] =
      app(app(get2nd, `false`), `true`)

    val apply1stOn2ndFn: Val[(Boolean => Boolean) => Boolean => Boolean] =
      lam[Boolean => Boolean, Boolean => Boolean](f => lam[Boolean, Boolean](x => app(f, x)))

    val apply1stOn2ndFnOnTuple: Trm[Boolean] =
      app(app(apply1stOn2ndFn, identityFn), `false`)

    val chooseFalse: Trm[Boolean] =
      app(app(app(ifThenElse, `false`), `true`), `false`)

    def run(): Unit = {
      assert(normalize(identityFnOnFalse) == `false`)
      assert(normalize(get1stOnTuple) == `false`)
      assert(normalize(get2ndOnTuple) == `true`)
      assert(normalize(apply1stOn2ndFnOnTuple) == `false`)
    }
  }
}

@main def runStlcSyntax(): Unit =
  STLC_syntax.Examples.run()
