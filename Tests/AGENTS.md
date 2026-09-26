# Test and example files for Syntax & Semantic Rules

This directory contains Scala examples of type system features and their AST representations in Lean 4.

## Conventions

- Test cases for a specific semantic rule should be enclosed in a section. For example, tests for `eval`
      should be written in:

```
section eval

end eval
```
- Theorems, propositions, and properties should be excluded from tests.
- Test assertions should use `example` and the `rfl` tactic when possible.

## Scala syntax demo

These files demonstrate Scala type system features. Each Lean AST should correspond to its Scala example:

- [TrmDemo.lean](STLC/TrmDemo.lean) ↔ [TrmDemo.scala](Example/TrmDemo.scala)
- [TypDemo.lean](STLC/TypDemo.lean) ↔ [TypDemo.scala](Example/TypDemo.scala)
- [ValDemo.lean](STLC/ValDemo.lean) ↔ [ValDemo.scala](Example/ValDemo.scala)

Prefer these Lean ASTs in other tests. Versions with and without type annotations are both valid.
