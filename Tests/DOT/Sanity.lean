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


def fals : TermClosed BoolT :=
  fun _ => .fals

def tru : TermClosed BoolT :=
  fun _ => .tru

def ident : TermClosed (BoolT ==> BoolT) :=
  fun _ => .abs (fun x => .var x)

def falsAgain : TermClosed BoolT :=
  fun _ => .app (ident _) (fals _)

def first : TermClosed (BoolT ==> BoolT ==> BoolT) :=
  fun _ => .abs (fun x => .abs (fun _y => .var x))

def second : TermClosed (BoolT ==> BoolT ==> BoolT) :=
  fun _ => .abs (fun _x => .abs (fun y => .var y))

def testFirst : TermClosed BoolT :=
  fun _ => .app (.app (first _) (fals _)) (tru _)

def testSecond : TermClosed BoolT :=
  fun _ => .app (.app (second _) (fals _)) (tru _)

def app : TermClosed ((BoolT ==> BoolT) ==> BoolT ==> BoolT) :=
  fun _ => .abs (fun f => .abs (fun x => .app (.var f) (.var x)))

def falsAgain2 : TermClosed BoolT :=
  fun _ => .app (.app (app _) (ident _)) (fals _)
