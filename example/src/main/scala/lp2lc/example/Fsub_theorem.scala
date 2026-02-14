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

    val term_before_step: Int = ((x: Int) => x + 1)(2)
    val term_after_step: Int = 2 + 1
    val same_type_after_reduction: Int = term_after_step
  }

  object `preservation_result` {

    /** full name: Preservation Result
      *
      * purpose: This is the proved theorem `preservation_result : preservation`
      * in Coq. It packages all supporting lemmas and concludes that one-step
      * reduction preserves typing for the whole System F<: calculus.
      */
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

    enum eval_state[+A] {
      case value(v: A)
      case can_step(next: () => eval_state[A])
    }

    val value_case: eval_state[Int] = eval_state.value(42)

    val step_case: eval_state[Int] =
      eval_state.can_step(() => eval_state.value(((x: Int) => x + 1)(2)))
  }

  object `canonical_form_abs` {

    /** full name: Canonical Form for Abstractions
      *
      * purpose: If a closed value has an arrow type, then it must be a lambda
      * abstraction. This inverts the typing/value assumptions and is used in
      * the application case of progress.
      */
  }

  object `canonical_form_tabs` {

    /** full name: Canonical Form for Type Abstractions
      *
      * purpose: If a closed value has a universal type (`forall`), then it
      * must be a type abstraction. This is used in the type-application case
      * of progress.
      */
  }

  object `progress_result` {

    /** full name: Progress Result
      *
      * purpose: This is the proved theorem `progress_result : progress` in
      * Coq. Together with preservation, it yields soundness: well-typed closed
      * terms never get stuck.
      */
  }
}
