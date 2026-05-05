package DTLC

object STLC_syntax {

  sealed trait Trm[A]

  object Trm {
    final case class Literal[A](code: String) extends Trm[A]
    final case class Lam[A, B](body: Trm[A] => Trm[B]) extends Trm[A => B]
    final case class App[A, B](fn: Trm[A => B], arg: Trm[A]) extends Trm[B]

    def literal[A](code: String): Trm[A] =
      Literal(code)

    def lam[A, B](body: Trm[A] => Trm[B]): Trm[A => B] =
      Lam(body)

    def app[A, B](fn: Trm[A => B], arg: Trm[A]): Trm[B] =
      App(fn, arg)

    def normalize[A](trm: Trm[A]): Trm[A] =
      trm match {
        case Literal(_) =>
          trm
        case Lam(_) =>
          trm
        case App(fn, arg) =>
          val arg1 = normalize(arg)
          normalize(fn) match {
            case Lam(body) =>
              normalize(body(arg1))
            case fn1 =>
              App(fn1, arg1)
          }
      }
  }

  object Examples {
    import Trm.*

    val `false`: Trm[Boolean] =
      literal("false")

    val `true`: Trm[Boolean] =
      literal("true")

    val ifThenElse: Trm[Boolean => Boolean => Boolean => Boolean] =
      literal("if")

    val identityFn: Trm[Boolean => Boolean] =
      lam[Boolean, Boolean](x => x)

    val identityFnOnFalse: Trm[Boolean] =
      app(identityFn, `false`)

    val get1st: Trm[Boolean => Boolean => Boolean] =
      lam[Boolean, Boolean => Boolean](x => lam[Boolean, Boolean](_ => x))

    val get2nd: Trm[Boolean => Boolean => Boolean] =
      lam[Boolean, Boolean => Boolean](_ => lam[Boolean, Boolean](y => y))

    val get1stOnTuple: Trm[Boolean] =
      app(app(get1st, `false`), `true`)

    val get2ndOnTuple: Trm[Boolean] =
      app(app(get2nd, `false`), `true`)

    val apply1stOn2ndFn: Trm[(Boolean => Boolean) => Boolean => Boolean] =
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
      assert(normalize(chooseFalse) == chooseFalse)
    }
  }
}

@main def runStlcSyntax(): Unit =
  STLC_syntax.Examples.run()
