
# Test and example files for Syntax & Semantic Rules

This directory contains some Scala show case of its type system features, and how to express them as AST in Lean 4 as a meta-language.

## Conventions

- test cases for a specific semantic rule should be enclosed in a section, e.g. for function "eraseType", its test cases should be in:
```
section eraseType

end eraseType
```
- theorem/proposition/property should be excluded from testing.