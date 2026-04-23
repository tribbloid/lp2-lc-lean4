package DOT

object DepFnAndStructural {
  import scala.reflect.Selectable.reflectiveSelectable

  type DepFnAndRecord = ((x: Any) => x.type) & { type A } // this does make sense as type A cannot refer to x

  // there is a difference between elaboration at definition-site and elaboration at call-site, the first one is most common

  // but for our problem (logic with type constructor and type that depends on depFn), the second becomes a necessity

  /*
   solution 1: dual binding! every function must be an object, it must define 2 bounded variables: arg & self.
   */

  /*
   solution 2: integrate the call-site elaboration semantic that can be used to fulfil many things (typeCtor and DepFnAndRecord)
  
   elaboration only translate one AST to another, it must be included in the soundness proof.

   call-site elaboration used to be frown upon because it can creep into runtime (with runtime error).
   */

  /**
    * for type constructor support: introducing evidence of congruence `===`:
    */

  trait ===[X, Y] // implying any (x: X) and (y: Y) must be congruent, X & Y are usually singleton type but not always.

  /**
    * So far there is no way to subsume it into other syntax (unlike co/contravarianceEv, which are just higher-order
    * <:<)
    *
    * deterministic functions:
    *   - path selector
    *   - type/evidence constructor
    *   - extension constructor
    *   - literal primitive operators (`2 + 2`)
    *
    * are merely functions that carries over `===` from 2 args to their results:
    */

  val pureFnExample = {

    def pureFn: Product => Tuple = ??? // the following is automatically attached:

    def ev[X <: Product, Y <: Product]: (X === Y) <:< (? === ?) = ???
    // right side should be (fn(x: X).type  === fn(y: Y).type) = ???
  }

  /**
    * DOT calculus is constrained to define dependent type by stable path selection exactly because it's deterministic
    * (same path selection on the same object always yield same result, such that assigning value to its own type
    * annotation is always safe in runtime)
    *
    *   - other deterministic functions are ignored.
    *   - all DOT syntax definitions spent huge effort on defining deep path selection (`v1.x.y.Z`):
    */

  trait Y { val z: Z; type Z }
  trait X { val y: Y }
  trait T1 { val x: X }

  val _ = {
    def fn(v1: T1): v1.x.y.Z = { // gDOT2020 AST (with multi-layer path selector)
      ???
    }
  }

  /**
    * This is absolutely lame, we should declare `ext(x).T` (type member of extension constructor `ext` applied to `x`)
    * as if it is `x.T`.
    *
    * The new evidence of congruence can help that. The deep path selection become just shallow path selection on the
    * function itself as a deterministic extension constructor.
    */

  val _ = {
    implicit class Fn(val v1: T1) {

      val x = v1.x
      val y = x.y
      type Z = y.Z

      def result: Z = ???
    }
  }

  /**
    * `Fn(v1).result: Fn(v1).result` works equally well.
    */

}
