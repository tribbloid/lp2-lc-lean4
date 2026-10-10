# Raw callback equality and contracted UId application

`Root.Binder.apply` opens a fixed body at `.inr ()` and structurally substitutes its receipt.
This contract supplies uniform receipt substitution by construction. The diagnostic below concerns
literal equality of unrestricted raw callbacks, beyond the observations made by UId operations.

[RawValInverse.lean](RawValInverse.lean) derives `False` from a hypothetical `KVEquiv` on all raw `Root.Val` values.
It uses only `rightInv`; `leftInv`, classical choice, new axioms, and proof placeholders are unnecessary.
Its receipt-sensitive callback selects the opposite body constructor after consulting the supplied lookup.
The observer invokes that callback directly at `.inl receipt`, which bypasses `Root.Binder.apply`.
Applying the raw inverse law at the diagonal value's receipt forces a Boolean to equal its negation.

That conditional raw-equality result is not a counterexample to contracted UId application.
The callback's `.inr ()` branch remains fixed, so `Root.Binder.apply` structurally substitutes only that branch.
The diagnostic establishes a scope distinction between raw callback equality and the binding semantics;
it does not establish that UId needs an additional uniformity condition.

The normalization examples show how the image `{value // ∃ source, AST.recarrier source id = value}`
represents canonical observations using ordinary Lean equality. This concerns the equivalence law's value
representation; uniform receipt substitution is already supplied by `Root.Binder.apply`.

Runtime receipt tagging is a separate property: deriving receipts from the shared lookup's right summand
fixes the value tag by construction, replacing the premise needed for an arbitrary `Lesser.upcastV`.
