package lp2lc.example

object Fsub_theorem {

  object `preservation` {

    /** full name: Preservation
      *
      * purpose: To show that if a term `e` has type `T` and `e` reduces to
      * `e'`, then `e'` also has type `T`. This ensures that the type of a term
      * is invariant under reduction, which is crucial for type safety. It
      * implies that "well-typed programs do not go wrong" in the sense that
      * they don't step into an ill-typed state.
      */

    // Scala example:
    // If we have `(x: Int) => x + 1` applied to `2`, it has type `Int`.
    // It reduces to `2 + 1`, which is `3`, which also has type `Int`.
  }

  object `progress` {

    /** full name: Progress
      *
      * purpose: To show that if a term `e` is well-typed, then either `e` is a
      * value (it has finished computing) or there exists a term `e'` such that
      * `e` reduces to `e'`. Combined with preservation, this guarantees that a
      * well-typed program never gets "stuck" (reaches a state that is not a
      * value and cannot make a step). This entails the soundness of the type
      * system.
      */
  }
}
