package lp2lc.example

trait MetaThreoryExample {

  trait Preamble {
    type In1 // first input argument
    type In2 // second input argument
    type In3 // third input argument
    // ...
  }

}
object MetaThreoryExample extends MetaThreoryExample {

  object `coq_name` extends Preamble {

    { // {{ case }}: {{ short explanation of feature }}
      // {{ demo in Scala code }}
      type Out = Any
    }
  }

}
