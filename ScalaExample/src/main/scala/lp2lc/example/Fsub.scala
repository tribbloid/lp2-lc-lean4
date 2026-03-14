package lp2lc.example

object Fsub extends MetaThreoryExample {

  /** CAUTION: pre-types are not types! Compilers should check if they are valid
    * or defective.
    */

  /** Pre-types -- 17
    */
  object `typ` extends Preamble {

    { // typ_top: top type
      type Out = Any
    }

    { // typ_bvar: bounded type variable with DeBruijn index
      def fn(v: Any): Unit = {
        type Out = v.type
      }
    }

    { // typ_fvar: free type variable
      trait TypeName
    }

    { // typ_arrow: function type
      type Out = In1 => In2
    }

    { // typ_all: bounded universal type (forall X <: T1. T2)
      def fn[X <: In1]: Unit = {
        type Out = X
      }
    }
  }

  /** Pre-terms -- 26
    */
  object `trm` extends Preamble {

    { // trm_bvar: bound term variable with DeBruijn index
      def fn(v: Any): Unit = {
        val out = v
      }
    }

    { // trm_fvar: free term variable
      val freeVar: In1 = ???
    }

    { // trm_abs: lambda abstraction (fun x:V => e1)
      val absOut = (x: In1) => x

      // trm_app: function application
      val x: In1 = ???
      val appOut: In1 = absOut(x)
    }

    { // trm_tabs: type abstraction (fun X <: V => e1)
      def tabsOut[X <: In1](x: X): X = x

      // trm_tapp: type application
      val tappOut: In1 => In1 = tabsOut[In1]
    }
  }

  /** Types as locally closed pre-types -- 83
    */
  object `type` extends Preamble {

    { // type_top: Any is a locally closed type
      type Out = Any
    }

    { // type_var: a free type variable is locally closed
      trait X
      type Out = X
    }

    { // type_arrow: arrow type is locally closed when both sides are
      trait T1
      trait T2
      type Out = T1 => T2
    }

    { // type_all: universally quantified type is locally closed
      trait T1
      def fn[X <: T1]: Unit = {
        type Out = X
      }
    }
  }

  /** Terms as locally closed pre-terms -- 99
    */
  object `term` extends Preamble {

    { // term_var: free variable is a term
      val x: In1 = ???
    }

    { // term_abs: lambda with well-formed param type is a term
      trait V
      val absOut: V => V = (x: V) => x

      // term_app: application of two terms is a term
      val e2: V = ???
      val appOut: V = absOut(e2)
    }

    { // term_tabs: type abstraction with well-formed bound is a term
      trait V
      def tabsOut[X <: V](x: X): X = x

      // term_tapp: type application of a term to a well-formed type is a term
      val tappOut: V = tabsOut[V](???)
    }
  }

  /** Bindings: subtyping and typing assumptions -- 123
    */
  object `bind` extends Preamble {

    { // bind_sub: X <: T (subtyping bound)
      trait T
      trait X extends T
    }

    { // bind_typ: x : T (typing assumption)
      trait T
      val x: T = ???
    }
  }

  /** Well-formed types in an environment -- 141
    */
  object `wft` extends Preamble {

    { // wft_top: Any is well-formed in any environment
      type Out = Any
    }

    { // wft_var: a type variable is well-formed if bound in the environment
      trait U
      trait X extends U
      type Out = X
    }

    { // wft_arrow: arrow type is well-formed when both components are
      trait T1
      trait T2
      type Out = T1 => T2
    }

    { // wft_all: universally quantified type is well-formed
      trait T1
      def fn[X <: T1]: Unit = {
        type Out = X
      }
    }
  }

  /** Well-formed environments -- 161
    */
  object `okt` extends Preamble {

    { // okt_empty: empty environment is well-formed
    }

    { // okt_sub: extending with a fresh subtype binding preserves well-formedness
      trait T
      trait X extends T
    }

    { // okt_typ: extending with a fresh value binding preserves well-formedness
      trait T
      val x: T = ???
    }
  }

  /** Subtyping relation -- 171
    */
  object `sub` extends Preamble {

    { // sub_top: every well-formed type is a subtype of Any
      trait S
      val out: Any = (??? : S)
    }

    { // sub_refl_tvar: subtyping is reflexive on type variables
      trait X
      val out: X = (??? : X)
    }

    { // sub_trans_tvar: subtyping is transitive through bounds
      trait U
      trait X extends U
      trait T extends U
      val out: T = (??? : X).asInstanceOf[T]
    }

    { // sub_arrow: function subtyping is contravariant in argument, covariant in result
      trait S1
      trait T2
      trait T1 extends S1
      trait S2 extends T2
      // (S1 => S2) <: (T1 => T2) because T1 <: S1 (contra) and S2 <: T2 (co)
      val out: T1 => T2 = (x: S1) => (??? : S2)
    }

    { // sub_all: bounded quantifier subtyping
      trait S1
      trait T1 extends S1
      def fn[X <: T1](x: X): X = x
      val out: T1 => T1 = (x: T1) => fn[T1](x)
    }
  }

  /** Typing relation -- 196
    */
  object `typing` extends Preamble {

    { // typing_var: variable lookup
      trait T
      val x: T = ???
      val out: T = x
    }

    { // typing_abs: lambda abstraction typing
      trait T1
      trait T2
      val absOut: T1 => T2 = (x: T1) => (??? : T2)

      // typing_app: function application typing
      val e2: T1 = ???
      val appOut: T2 = absOut(e2)
    }

    { // typing_tabs: type abstraction typing
      trait T1
      def tabsOut[X <: T1](x: X): X = x

      // typing_tapp: type application typing, instantiation with subtype
      trait T extends T1
      val tappOut: T = tabsOut[T](???)
    }

    { // typing_sub: subsumption (if e : S and S <: T then e : T)
      trait T
      trait S extends T
      val e: S = ???
      val out: T = e
    }
  }

  /** Values -- 224
    */
  object `value` extends Preamble {

    { // value_abs: a lambda abstraction is a value
      trait V
      val out: V => V = (x: V) => x
    }

    { // value_tabs: a type abstraction is a value
      trait V
      def out[X <: V](x: X): X = x
    }
  }

  /** One-step reduction -- 232
    */
  object `red` extends Preamble {

    { // red_app_1: reduce function position in application
      trait T1
      trait T2
      def e1(x: T1): T2 = ???
      def e1prime(x: T1): T2 = ???
      // if e1 -> e1', then (e1 e2) -> (e1' e2)
      val e2: T1 = ???
      val before: T2 = e1(e2)
      val after: T2 = e1prime(e2)
    }

    { // red_app_2: reduce argument position in application
      trait T1
      trait T2
      val e1: T1 => T2 = (x: T1) => ???
      // if e2 -> e2', application reduces in argument
      val e2: T1 = ???
      val e2prime: T1 = ???
      val before: T2 = e1(e2)
      val after: T2 = e1(e2prime)
    }

    { // red_tapp: reduce under type application
      trait T1
      trait V extends T1
      def e1[X <: T1](x: X): X = ???
      def e1prime[X <: T1](x: X): X = ???
      // if e1 -> e1', then (e1 [V]) -> (e1' [V])
      val before: V = e1[V](???)
      val after: V = e1prime[V](???)
    }

    { // red_abs: beta reduction ((\x:V. e1) v2) -> e1[x := v2]
      trait V
      val out: V => V = (x: V) => x
      val v2: V = ???
      val reduced: V = out(v2)
    }

    { // red_tabs: type beta reduction ((\X<:V1. e1) [V2]) -> e1[X := V2]
      trait V1
      def out[X <: V1](x: X): X = x
      trait V2 extends V1
      val reduced: V2 = out[V2](???)
    }
  }
}
