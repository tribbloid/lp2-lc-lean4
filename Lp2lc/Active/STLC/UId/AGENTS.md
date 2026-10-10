# PL semantics

This module uses untyped UIds and key-value equivalence for variable binding.

- Compile-time receipts are obtained through `KVEquiv.inv`.
- Runtime receipts certify shared lookup of the requested canonical value; with a build environment,
      its inverse laws determine that same receipt.
- UId operations must open functional binders only at `.inr ()` and structurally substitute receipts into that body.
