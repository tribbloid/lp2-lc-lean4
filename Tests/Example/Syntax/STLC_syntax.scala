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

    def eval[A](trm: Trm[A], fuel: Int): Option[Val[A]] = // AKA normalise, result is also an AST
      if fuel <= 0 then None
      else
        trm match {
          case literal: Literal[a] =>
            Some(literal)
          case lam: Lam[a, b] =>
            // TODO: HOAS body can only be evaluated into Val after an argument is supplied.
            Some(lam)
          case App(fn, arg) =>
            for {
              case Lam(body) <- eval(fn, fuel - 1)
              arg1 <- eval(arg, fuel - 1)
              result <- eval(body(arg1), fuel - 1)
            } yield result
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
      assert(eval(`false`, 0).isEmpty)
      assert(eval(identityFnOnFalse, 1).isEmpty)
      assert(eval(identityFnOnFalse, 2).contains(`false`))
      assert(eval(get1stOnTuple, 3).contains(`false`))
      assert(eval(get2ndOnTuple, 3).contains(`true`))
      assert(eval(apply1stOn2ndFnOnTuple, 4).contains(`false`))
      assert(eval(chooseFalse, 4).isEmpty)
    }
  }
}

@main def runStlcSyntax(): Unit =
  STLC_syntax.Examples.run()
