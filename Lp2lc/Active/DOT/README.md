
Conventions:

- PHOAS (parametric higher order abstract syntax), term/type indices are
  irrelevant, no de Bruijn serial or explicit variable name allowed
- All typing/subtyping/variance relations are evidence (a special kind of
  term)! This includes:
    - typing: t : T
    - subtyping: T1 <:< T2
    - variance for type constructors: [+I] => T[I], [-I] => T[I]
- Extrinsic typing, in pCIC a type cannot be indexed by another type in the same
  mutual block which makes intrinsic typing IMPOSSIBLE. Types still exist in
  term constructors, but they are evaluated much later.
- The modeled Scala subset is purely functional and stateless, with structural objects/records, so:
    - No let-binding! Binding uses `Val.depFn` and `Trm.depApply`.
    - Explicit Env/Context/Store is just a collection of all 3 kinds of evidence
    (backed by Heyting lattice).

    It's an IR built from an AST and nothing else, but it's an
    important one. Without it we may never be able to infer the equality of
        - `type A; type B <: A`, and
        - `type B; type A >: B`
- We haven't reached variance yet, so both `Typ.depFn` and `Evidence.subtypeEv` are
  invariant (IRL they are 1-contravariant and 2-covariant, but we will get
  there)
- Runtime values use `Val`; its `evidence` constructor can still carry type information through `Evidence`.
- Currying is always enabled, a binary operation is folded into curried form of 2
  unary operations.

The most iconic part of PHOAS is the "(I : Type)" argument in every definition,
it is used whenever an unknown symbol is used to construct a new AST in Scala,
e.g.

```scala
def fn: Int => Int = { x => // <- introducing x (bound variable)
  x + 1
}

trait T1 { // <- introducing T1.this (self-binder, or is it "bounded self"?)
  trait T2 { // <- introducing T2.this
    def breadcrumb = T1.this.toString + "." + T2.this.toString
  }
}

type DepFn = { (x: HList) => // <- introducing x (bounded variable)
  x.Arity
}

type K1[T] = // <- introducing T (bounded type argument)
  Option[T] | List[T]

```

in PHO-AST the unknown argument corresponds to "(body : (arg: I) -> ???)" in a
constructor, the "I" cannot be hardcoded into a concrete type because it may
break strict positivity constraint and allow `body` to abuse its metadata.
