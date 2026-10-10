# Raw functional values cannot have a total receipt inverse

[RawValInverse.lean](RawValInverse.lean) derives `False` from `KVEquiv` on the current unrestricted UId value family.
It uses only `rightInv`; `leftInv`, classical choice, new axioms, and proof placeholders are unnecessary.

A function value can inspect its callback input `.inl receipt`, decode that receipt through the supplied lookup,
and select the opposite body constructor. Applying the inverse law to this diagonal value and observing its
callback at its own receipt forces a Boolean to equal its negation. The canonical `.inr ()` body remains fixed.

Restricting runtime operations to canonical opening cannot justify raw value equality in `KVEquiv.rightInv`.
A structural binder stores syntax and has no callback that can inspect this receipt. A quotient-free repair
must use structural values or limit the admitted value family to canonical values before declaring the
ordinary `KVEquiv` contract.

The normalization observation in the same test confirms that arbitrary behavior at `.inl receipt` is erased.
The image `{value // ∃ source, AST.recarrier source id = value}` therefore admits the canonical observation
rather than the original callback. Constructing membership requires only the source and reflexivity.
Deriving runtime receipts from the shared lookup's right summand fixes the payload tag by construction;
an arbitrary `Lesser.upcastV` cannot provide that guarantee without an additional premise.
