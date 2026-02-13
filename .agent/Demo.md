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
 * cases:
 * 
 * typ_top / type_fvar / ...
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

  // typ_top: top type
  {
    type _ = Any
  }

  // typ_bvar: new unbounded type with DeBrujin index
  {
    trait _1
  }

  // typ_fvar: new unbounded type with name
  {
    trait TypeName
  }

  // typ_arrow: function type
  {
    type In1
    type In2
    
    type _ = In1 => In2
  }

  // typ_all: upper bound / ForAll
  {
    type In1
    type In2
    
    type _ = In2 & In1
    type _ = In2 {given ev: this.type <:< In1}
  }
}
```

## Verify

- Doublecheck that:
    -[ ] All Coq types are demoed in Scala code.
    -[ ] gradle can compile Scala code without error.
