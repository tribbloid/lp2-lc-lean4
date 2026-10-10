# PL semantics

This module uses untyped UIds and key-value equivalence for variable binding.

- Receipts are assumed to be obtained through `KVEquiv.inv`.
- UId operations must open functional binders only at `.inr ()` and structurally substitute receipts into that body.
