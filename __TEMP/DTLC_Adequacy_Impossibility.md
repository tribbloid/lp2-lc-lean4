# DTLC Adequacy Proof Blocker

The requested global adequacy theorem for the current `AST.Trm.IsAdequate`
definition is false.

`AST.Trm.compile` now satisfies the existing DTLC compile tests, including the
malformed application canaries, but the current type information tracked by the
compiler is not strong enough to prove that every successfully compiled program
avoids runtime `.error`.

## Counterexample

The following closed source term is accepted by `compile 3` but its compiled
program evaluates to `.error` at runtime fuel `3`.

```lean
def badFn : Trm :=
  .val (.fn (fun x => .apply (.ref x) (.ref x)))

def escapedBadFnOnFalse : Trm :=
  .apply (.apply idFn badFn) false
```

The compiler result is definitionally:

```lean
escapedBadFnOnFalse.compile 3 =
  .result
    (.apply
      (.apply (idFn.type.eraseRecursively) (badFn.type.eraseRecursively))
      (false : Trm))
```

The compiled program then evaluates to runtime `.error`:

```lean
((.apply
    (.apply (idFn.type.eraseRecursively) (badFn.type.eraseRecursively))
    (false : Trm) : Trm).eval 3) = .error
```

Therefore `escapedBadFnOnFalse.IsAdequate 3` cannot be proved.

## Why This Happens

`badFn` is a function value, so compiling the value itself succeeds. The bad
body is only exercised after `badFn` escapes through `idFn` and is applied to
`false`.

The current compiler tracks only a single `boundType : Option (Typ I)` while
checking references. That is enough for the existing tests, but it cannot
distinguish multiple HOAS references in nested functions or preserve the
application obligation for a function value after it has been returned by
another term.

Consequently, the compiler can assign the escaped function position a dependent
function type and accept the final application, even though runtime evaluation
reaches a primitive-as-function application inside `badFn`.

## Verified State

The compiler implementation itself was verified with:

```text
lake build Lp2lc.Active.DTLC.Def
lake build Tests.DTLC.TrmSpec
lake build Lp2lc.Active.DTLC.Proof
lake build
git diff --check
```

All existing tests pass without changing test conditions.
