
### General Rules
see [this](../AGENTS.md)

### Conversion Rules
- Compile the project
- Preserve original names (add `def_` prefix only if required by Lean syntax) and orders.
- Prefix each declaration with a comment indicating original Coq line number (strictly incremental).
- Use "sorry" with "TODO" comment for incomplete proofs.
- `Set`/`Prop` → Lean `Prop`.
- `Type` → Lean `Prop` (avoid `Type` unless necessary).
- `Var` from LibLN → Lean structure with `String` field.
- `Hint Constructors` → `@[aesop constructor]` attribute on type constructor.
- `Hint Resolve` → `@[aesop]` attribute on function (create wrapper functions if needed).
- `Lemma` → `Theorem`.
- `Tactic Notation` → Lean tactic macro with examples.
- `Ltac` → Lean elaborator with examples.
- `LibEnv` lemma reference `ok E` → a minimal abstract `ok : env → Prop` in `Aux.lean` to keep statements typechecking.

### Success Criteria
- Complete 1:1 conversion of all declarations.
- Proofs verified or explicitly marked as incomplete.
