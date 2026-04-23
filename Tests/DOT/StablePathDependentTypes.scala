package DOT

object StablePathDependentSanity {
  import scala.reflect.Selectable.reflectiveSelectable

  // object StructuralTyping {

  //   type T1 = { val x: { val y: { val z: Z; type Z } } }

  //   def fn1(v1: T1): v1.x.y.Z = { // gDOT2020 AST (with multi-layer path selector)
  //     v1.x.y.z: v1.x.y.Z
  //   }

  //   def fn2(v1: T1): v1.x.y.Z = { // WadlerFest2016 AST (with let-binding)
  //     val x: v1.x.type = v1.x
  //     val y: x.y.type = x.y
  //     type Z = y.Z
  //     y.z: Z
  //   }

  //   def fn3(v1: T1): v1.x.y.Z = { // local object AST (with lazy recursive self-binding)
  //     object State {
  //       lazy val x: v1.x.type = v1.x
  //       lazy val y: x.y.type = x.y
  //       type Z = y.Z
  //       lazy val z: Z = y.z
  //     }

  //     State.z
  //   }
  // }

  object NominalTyping {

    trait Y { val z: Z; type Z }
    trait X { val y: Y }
    trait T1 { val x: X }

    def fn1(v1: T1): v1.x.y.Z = { // gDOT2020 AST (with multi-layer path selector)
      v1.x.y.z: v1.x.y.Z
    }

    def fn2(v1: T1): v1.x.y.Z = { // WadlerFest2016 AST (with let-binding)
      val x: v1.x.type = v1.x
      val y: x.y.type = x.y
      type Z = y.Z
      y.z: Z
    }

    def fn3(v1: T1): v1.x.y.Z = { // local object AST (with lazy recursive self-binding)
      object State { // merge these 2 binders (arg & self) to make State referrable from outside!
        lazy val x: v1.x.type = v1.x
        lazy val y: this.x.y.type = x.y
        type Z = this.y.Z
        lazy val z: Z = y.z
      }

      State.z
    }

    // case class Fn4(v1: T1) extends (() => Any) {
    //   lazy val x: v1.x.type = v1.x
    //   lazy val y: this.x.y.type = x.y
    //   type Z = this.y.Z
    //   lazy val z: Z = y.z
    // }

    // def fn4(v1: T1): Fn4(v1).Z = {
    //   Fn4(v1).z
    // }

    // type Fn5 = ((v1: T1) => v1.x.y.Z) with {

    //   val v1: T1

    //   val x: v1.x.type
    //   val y: x.y.type
    //   type Z
    //   val out: Z
    // }

    // def fn4: Fn4 = { (v1: T1) =>
    //   val x: v1.x.type = v1.x
    //   val y: x.y.type = x.y
    //   type Z = y.Z
    //   y.z: Z
    // }

    // def fn4: Fn4 = { v1 =>
    //   val x: v1.x.type = v1.x
    //   val y: x.y.type = x.y
    //   type Z = y.Z
    //   y.z: Z
    // }
  }
}
