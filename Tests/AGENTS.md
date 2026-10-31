# Test and example files for Syntax & Semantic Rules

This directory contains Lean 4 tests and examples of type system features, with corresponding Scala examples.

## Conventions

- Test cases for a specific semantic rule should be enclosed in a section. For example, tests for `eval` should be
      written in:

```
section eval

end eval
```

- Theorems, propositions, and properties should be excluded from tests.
- Test assertions should use concise `#guard` expressions, sharing repeated setup and checks.

## Scala Syntax demo

The shared Scala files in `Tests/Example` demonstrate the AST fixtures in the mature STLC, STLC_minimal, DTLC,
and DSub test modules. Maintain the following mapping from each module's Lean demos to these Scala demos:

- TrmDemo.lean ↔ TrmDemo.scala
- TypDemo.lean ↔ TypDemo.scala
- ValDemo.lean ↔ ValDemo.scala
- The Lean `Trm`, `Typ`, and `Val` namespaces correspond to the Scala `TrmDemo`, `TypDemo`, and `ValDemo` objects.
- Nested Lean namespaces (e.g. `Malformed` and `Corrupted`) correspond to identically named Scala objects.

Add every new test AST to its Lean demo and the corresponding Scala demo at the same time, preserving its name,
term structure, and type annotation. Share a Scala example when the Lean modules use the same fixture. Runtime
test helpers and disabled fixtures do not need Scala counterparts.

Scala rejects the intentionally malformed ASTs and cannot express a primitive callback that breaks its declared
result type without a cast. Keep these examples lazy and make the required casts explicit in `Malformed` or
`Corrupted`, so loading the demo does not evaluate an expected failure.

Prefer these Lean ASTs in other tests. Versions with and without type annotations are both valid.
