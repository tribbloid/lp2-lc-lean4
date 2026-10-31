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

These files demonstrate Scala type system features. For each type system module (e.g. STLC or DSub).
The mapping from Lean demo file structure to the Scala demo file structure must be maintained.

- TrmDemo.lean ↔ TrmDemo.scala
- TypDemo.lean ↔ TypDemo.scala
- ValDemo.lean ↔ ValDemo.scala
- `namespace Xxx` in Lean ↔ `object Xxx` in Scala

Every new AST definition for testing should be added into both Lean demo and Scala demo (if not exists) at the
same time:

Prefer these Lean ASTs in other tests. Versions with and without type annotations are both valid.
