# Demo Steps

## Locate Coq proof file

## List Coq types as Scala objects

- convert each Coq type definition into to a Scala object in the root object
- name of the root object should be identical to file name.
- follow Scala 3.3 syntax.
- e.g. Coq type `Inductive typ` should become:

```Scala
/**
 * <short explanation> -- <Coq line number>
 * 
 * including cases:
 * 
 * - typ_top
 * - type_fvar
 * ...
 */
object `typ` {
}
```

## Writing Scala Examples

- In each Scala object, explain the Scala language feature defined by Coq cases
- search https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/coqdoc and other coq documents for symbols you don't know
- e.g. Coq type `Inductive typ` should be explained as:

```scala
object `typ` {

  // typ_top
  (_: Any) // typ_top

  // typ_fvar
  trait Var
  
  // typ_all
  {
    trait T0
    trait ForAll[T1 <: T0]
  }
}

{ /* Coq definition name - Coq line number */
  
  // (using `Inductive typ` as an example)
  (_: Any) // typ_top
  
  trait SomeName // type_fvar
  // ... (each inductive cases should have its own example)
}
```

## Verify

- Doublecheck that:
    -[ ] All Coq types are demoed in Scala code.
    -[ ] gradle can compile Scala code without error.
