# Demo Steps

## Locate Coq proof file

## Writing Scala Demo

- each Coq type defines a Scala feature.
- each feature should be demonstrated in a Scala code block in the root object.
  - the code block should look like this:
```scala
{ /* lean name - lean line number */
  
  // (using `Inductive typ` as an example)
  (_: Any) // typ_top
  
  trait SomeName // type_fvar
  // ... (each inductive cases should have its own example)
}
```
- name of the root object should be identical to file name.
- follow Scala 3.3 syntax.

## Verify

- Doublecheck that:
    -[ ] All Coq types are demoed in Scala code.
    -[ ] gradle can compile Scala code without error.
