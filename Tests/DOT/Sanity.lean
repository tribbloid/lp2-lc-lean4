import «Lp2lc».Active.DOT.Def

/-
this is a supporting sanity test file for DOT calculus definition.

Conventions:

- PHOAS (parametric higher order abstract syntx), term/type indices are
  irrelevant, no de Bruijn serial or explicit variable name allowed
- All typing/subtyping/variance relations are evidences (a special kind of
  term)! These includes:
  - typing: t : T
  - subtyping: T1 <:< T2
  - variance for type constructors: [+I] => T[I], [-I] => T[I]
- Intrinsic typing but they are just built-in evidences/axioms for the symbol,
  they don't participate in judgement of inhabitance or well-typedness (these
  are still extrinsic).
- Scala is purely functional, stateless with structural object/record, so:
  - No let-binding! (exists in Wadler 2016 but was quickly removed), binding is
    just monoFn/monoApply with side effects on the record of local variables
  - Explicit Env/Context/Store is just a collection of all 3 kinds of evidences
    (backed by Heyting lattice).

    It's only an IR built from only a AST tree and nothing else, but it's an
    important one. Without it we may never be able to infer the equality of
    - `type A; type B <: A`, and
    - `type B; type A >: B`
- We haven't reach variance yet, so both Function and SubtypeEvidence are
  invariant (IRL they are 1-contravariant and 2-covariant, but we will get
  there)
- Type erasure: Val do NOT carry any type information
- Currying is always enabled, a binary operation is fold into curried form of 2
  unary operations.

The most iconic part of PHOAS is the "(I : Type)" argument in every definition,
it is used whenever an unknown symbol is used to construct a new AST in Scala,
e.g.

```scala
def fn: Int => Int = { x => // <- introducing x (bounded variable)
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
constructor, the "I" cannot be hardcoded into a concrete type because it may break strict
positivity constraint and allow `body` to abuse its metadata.

-/

namespace Tests.DOT.Sanity
open Lp2lc.Active.DOT

namespace Trm

def false : TrmClosed :=
  .val (.primitive "false")

def true : TrmClosed :=
  .val (.primitive "true")

def identityFn : TrmClosed :=
  .val
    (.depFn (fun x => .var x))

def identityFnOnFalse : TrmClosed :=
  .depApply identityFn false

def get1st : TrmClosed :=
  .val
    (.depFn (fun x =>
      .val
        (.depFn (fun _y => .var x))))

def get2nd : TrmClosed :=
  .val
    (.depFn (fun _x =>
      .val
        (.depFn (fun y => .var y))))

def get1stOnTuple : TrmClosed :=
  .depApply
    (.depApply get1st false)
    true

def get2ndOnTuple : TrmClosed :=
  .depApply
    (.depApply get2nd false)
    true

def apply1stOn2ndFn : TrmClosed :=
  .val (.depFn (fun f =>
    .val (.depFn (fun x =>
      .depApply
        (.var f)
        (.var x)))))

def apply1stOn2ndFnOnTuple : TrmClosed :=
  .depApply
    (.depApply apply1stOn2ndFn identityFn)
    false

end Trm
end Sanity
