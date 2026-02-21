package lp2lc.example

object Fsub extends MetaThreoryExample {

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

  }
}
