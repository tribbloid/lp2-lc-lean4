package lp2lc.example

object Fsub {

  { /* typ - Fsub.v:17 */

    // typ_top
    (_: Any)

    // typ_bvar
    // de Bruijn indices are usually not exposed in high-level Scala

    // typ_fvar
    trait X

    // typ_arrow
    (_: Int => String)

    // typ_all
    // forall X <: T1, T2
    // Scala uses higher-kinded types or path-dependent types for some forms of polymorphism,
    // but strict Fsub bounded quantification is often approximated or modeled.
    // A simplified view:
    trait T1
    def poly[X <: T1](x: X): X = x
  }

  { /* trm - Fsub.v:26 */

    // trm_bvar

    // trm_fvar
    val x = 1

    // trm_abs
    val abs = (y: Int) => y + 1

    // trm_app
    abs(1)

    // trm_tabs
    // Type abstraction
    def tabs[X] = (x: X) => x

    // trm_tapp
    // Type application
    tabs[Int]
  }

  { /* bind - Fsub.v:123 */
    // bind_sub
    // X <: T
    type X <: Any

    // bind_typ
    // x : T
    val x: Int = 1
  }
}
