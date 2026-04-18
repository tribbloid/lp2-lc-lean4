# subtype lattice in PHOAS?

The biggest obstacle to simplification is a data structure representing
type symbols with their subtype lattice, which:

- always have top & bottom
- is composible, multiple lattices can be merged together
- can be composed by traversing the AST. The subtyping reference graph is never a tree, e.g.:
    ```scala
    type A <: B
    type B >: A
    ```
    is perfectly valid but contains circular definition, it is only expressed in AST because different nodes are discovered to be the same thing later.

Fortunately, it is impossible to define type alias outside object in DOT, and it only become a type alias when explicitly invoked, this means the most complex subtype lattice only needs to be defined inside an object, e.g.:

```scala
trait T1 {
  type X >: Tuple1 <: Product
}
```

becomes:

```scala
trait T1 {
  type X // just a symbol
  given Tuple1 <:< X // nameless
  given X <:< Product // nameless
}
```

which is interpreted by:
```lean
.and
  "X" ~ .object1 .typeAlias "X"
  .and
    "" ~ .term .subtypeEv Tuple1 `(x : .self).X`
    "" ~ .term .subtypeEv `(x : .self).X` Product
```

