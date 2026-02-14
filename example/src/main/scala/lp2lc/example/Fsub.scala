package lp2lc.example

object Fsub {

  /**
   * Pre-types -- 17
   *
   * cases:
   * - typ_top
   * - typ_bvar
   * - typ_fvar
   * - typ_arrow
   * - typ_all
   */
  object `typ` {

    // typ_top
    type Top = Any

    // typ_bvar
    type DeBruijnIndex = Int

    // typ_fvar
    trait Animal
    trait Dog extends Animal

    // typ_arrow
    val arrow: Dog => Animal = (d: Dog) => d

    // typ_all
    def forAll[T <: Animal](v: T): Animal = v
  }

  /**
   * Pre-terms -- 26
   *
   * cases:
   * - trm_bvar
   * - trm_fvar
   * - trm_abs
   * - trm_app
   * - trm_tabs
   * - trm_tapp
   */
  object `trm` {

    // trm_bvar
    type BoundVar = Int

    // trm_fvar
    val x: Int = 42

    // trm_abs
    val abs: Int => Int = (n: Int) => n + 1

    // trm_app
    val app: Int = abs(x)

    // trm_tabs
    def tabs[A](a: A): A = a

    // trm_tapp
    val tapp: String = tabs[String]("hello")
  }

  /**
   * Locally closed types -- 83
   *
   * cases:
   * - type_top
   * - type_var
   * - type_arrow
   * - type_all
   */
  object `type` {

    // type_top
    type Top = Any

    // type_var
    trait Alpha

    // type_arrow
    type Arrow = Alpha => Top

    // type_all
    trait Bound
    type ForAll = [T <: Bound] =>> T => Bound
  }

  /**
   * Locally closed terms -- 99
   *
   * cases:
   * - term_var
   * - term_abs
   * - term_app
   * - term_tabs
   * - term_tapp
   */
  object `term` {

    // term_var
    val freeVar: Int = 1

    // term_abs
    val lambda: Int => Int = (n: Int) => n

    // term_app
    val applied: Int = lambda(freeVar)

    // term_tabs
    def poly[A](a: A): A = a

    // term_tapp
    val specialized: String = poly[String]("hello")
  }

  /**
   * Environment bindings -- 123
   *
   * cases:
   * - bind_sub
   * - bind_typ
   */
  object `bind` {

    // bind_sub: subtyping assumption X <: T
    trait Fruit
    trait Apple extends Fruit

    // bind_typ: typing assumption x : T
    val x: Fruit = new Apple {}
  }

  /**
   * Environment alias -- 134
   *
   * env is an association list of bindings.
   */
  object `env` {
    type Assoc[K, V] = List[(K, V)]
    type Env = Assoc[String, bind.Fruit]
  }

  /**
   * Well-formed types in environment -- 141
   *
   * cases:
   * - wft_top
   * - wft_var
   * - wft_arrow
   * - wft_all
   */
  object `wft` {

    // wft_top
    type WfTop = Any

    // wft_var
    trait Bound
    trait X extends Bound

    // wft_arrow
    type WfArrow = X => Bound

    // wft_all
    type WfAll = [T <: Bound] =>> T => Bound
  }

  /**
   * Well-formed environments -- 161
   *
   * cases:
   * - okt_empty
   * - okt_sub
   * - okt_typ
   */
  object `okt` {

    // okt_empty
    type Empty = EmptyTuple

    // okt_sub
    trait Animal
    trait Cat extends Animal

    // okt_typ
    val cat: Animal = new Cat {}
  }

  /**
   * Subtyping relation -- 171
   *
   * cases:
   * - sub_top
   * - sub_refl_tvar
   * - sub_trans_tvar
   * - sub_arrow
   * - sub_all
   */
  object `sub` {

    trait Top

    // sub_top
    trait S extends Top

    // sub_refl_tvar
    trait X
    val refl: X => X = identity

    // sub_trans_tvar
    trait U extends Top
    trait TransX extends U

    // sub_arrow
    trait A
    trait B extends A
    trait C
    trait D extends C
    val arrowSub: (A => D) => B => C = (f: A => D) => (b: B) => f(b)

    // sub_all
    trait Bound1
    trait Bound2 extends Bound1
    def allSub[T <: Bound1](v: T): Bound1 = v
  }

  /**
   * Typing relation -- 196
   *
   * cases:
   * - typing_var
   * - typing_abs
   * - typing_app
   * - typing_tabs
   * - typing_tapp
   * - typing_sub
   */
  object `typing` {

    trait Gamma

    // typing_var
    val x: Int = 1

    // typing_abs
    val abs: Int => String = (n: Int) => n.toString

    // typing_app
    val app: String = abs(x)

    // typing_tabs
    def tabs[A <: Gamma](a: A): Gamma = a

    // typing_tapp
    class G extends Gamma
    val tapp: Gamma = tabs[G](new G)

    // typing_sub
    val sub: Any = app
  }

  /**
   * Values -- 224
   *
   * cases:
   * - value_abs
   * - value_tabs
   */
  object `value` {

    // value_abs
    val absVal: Int => Int = (n: Int) => n + 1

    // value_tabs
    def tabsVal[A](a: A): A = a
  }

  /**
   * One-step reduction -- 232
   *
   * cases:
   * - red_app_1
   * - red_app_2
   * - red_tapp
   * - red_abs
   * - red_tabs
   */
  object `red` {

    // red_app_1
    val e1: Int => Int = (n: Int) => n * 2
    val e2: Int = 3

    // red_app_2
    val v1: Int => Int = (n: Int) => n + 1
    val appResult: Int = v1(e2)

    // red_tapp
    def tapp[A](f: A => A, a: A): A = f(a)

    // red_abs
    val beta: Int = ((n: Int) => n + 1)(5)

    // red_tabs
    def typeBeta[A](a: A): A = identity[A](a)
    val reduced: Int = typeBeta[Int](42)
  }
}
