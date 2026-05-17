
# Test and example files for Syntax & Semantic Rules

This directory contains some Scala show case of its type system features, and how to express them as AST in Lean 4 as a meta-language.

## Conventions

- test cases for a specific semantic rule should be enclosed in a section, e.g. for function "eraseType", its test cases should be in:
```
section eraseType

end eraseType
```
- theorem/proposition/property should be excluded from testing.
- test assertions should use `example` (always) and `rfl` tactic (if possible)
- unsafe code is permitted

## Scala syntax demo

The following code are for demonstration of Scala type system, examples in them must have strict correspondence between Lean AST and Scala code example:

- "TrmDemo.lean" <-> "Example/TrmDemo.Scala"
- "TypDemo.lean" <-> "Example/TypDemo.Scala"
- "ValDemo.lean" <-> "Example/ValDemo.Scala"

Using these Lean AST are preferred in other test code. It should be noted that each AST may include versions with or without type annnotation, both are valid and should not be perceived as duplicates.