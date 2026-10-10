# PL semantics

This module uses untyped UIds and key-value equivalence for variable binding.

- Compile-time type receipts and runtime value receipts come from the same `BuildEnv` equivalence over
      the shared `Typ ⊕ Val` context.
- Runtime receipts certify lookup of the exact value in that context.
- UId operations must open functional binders only at `.inr ()` and structurally substitute receipts into that body.
