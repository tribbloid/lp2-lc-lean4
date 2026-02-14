package lp2lc.example

object Fsub {

  trait Preamble {
    type In1 // first input argument
    type In2 // second input argument
    type In3 // third input argument
    // ...
  }

  /** This object is a template for all the following examples
    *
    * "short explanation of type system feature" -- "coq name"
    */
  object `coq_name` extends Preamble {

    { // "first_case": "short explanation"
      // type system demo in Scala code
    }
  }

  // examples start here

  /** Pre-types -- 17
    */
  object `typ` extends Preamble {

    { // typ_top: top type
      type Out = Any
    }

    { // typ_bvar: new unbounded type with DeBrujin index
      trait _1
    }

    { // typ_fvar: new unbounded type with name
      trait TypeName
    }

    { // typ_arrow: function type
      type Out = In1 => In2
    }

    { // typ_all: ForAll / upper bound type
      type Out = In1 & In2
    }
  }
}
