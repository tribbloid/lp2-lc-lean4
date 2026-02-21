package lp2lc.example

trait MetaThreoryExample {

  trait Preamble {
    type In1 // first input argument
    type In2 // second input argument
    type In3 // third input argument
    // ...
  }

  private object `coq_name` extends Preamble {

    { // {{ case }}: {{ short explanation of language feature / inference rule }}
      // {{ demo in Scala code, inference result should always be "Out" (for type) or "out" (for term) }}
      type Out = Any
    }
  }

}
object MetaThreoryExample extends MetaThreoryExample {}
