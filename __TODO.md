# Convention

in HOAS, functions in Scala (object-language) is usually represented by constructs that contains funtions in Lean (meta-language). To differentiate them, we use "fn" to denote former and "function" to denote later.

# Compiletime-runtime boundary

the most difficult part of HOAS repr is that it is hard to enforce 2 rules to 1 AST:

- compilletime cannot execute most code (assumed to be non-pure & interacting with IO)
    - transparent fns are exception (not inline fns! they are subjected to normal typing rule)
- runtime cannot see most types
    - classTag/typeTag are exception
- both are recursive and uses fuel

There are some very weird fns in Scala (see __ExoticFunctions.scala), they all fit under .fn syntax, with subtle differences:

- inline fn can be evaluated in compiletime, but eval result won't affect typing
- transparent fn only affect typing at its call-site (outside DOT)
- none can produce refined type or affect typing at its define-site
- despite that, eval in compiletime can produce compiletime evidence (e.g. of congruence)! This will be a macro outside DOT 

So **for a normal fn**: what happens if it is applied on a constant?

- compiletime: the fn call a function `F := T -> (Trm[T], RF)` on input type (including path identity) of the constant without `runtimeStagePermission` (it won't be provided at this stage), but not actual data. This function produce:
    1. a `Trm[T]` that can be reduced to its output type.
    2. the runtime function `RF := (runtimeStagePermission, D) -> Trm[D]`, the `Trm[D]` has to be compatible with `Trm[T]` defined previously
- runtime: the function produce `Trm[D]`.

**The problem is**: how to make them compatible?

ideally fnAST is a generator: compiletimeFunction <- fnAST -> runtimeFunction:

- compiletimeFunction:
    - can always be applied on input type (even Singleton types) and yield `Trm[T]`
    - (not in DOT) if transparent inline, can be applied on input term
    - `Trm[T]` -> `Trm[D]` is strictly forbidden
- runtimeFunction:
    - can always be applied on input value and yield `Trm[D]`

there are 3 ways to enforce this discipline (no eval at compiletime):

- [x] permission to use function body `body: StagePermission -> I -> Trm` (most promising, what's the caveat?)
- [ ] permission to save Value to FBoundV2 `save: StagePermission -> Val -> I` (or just withhold instances of FBoundV2)
- [ ] permission to load Value from FBoundV2 `load: StagePermission -> I -> Val`



# Weakening of Goalpost

Current AST always assumes optional type hint (mimicking env in locally-nameless repr), what if I broke it into 2 problems: type hint inference and compilation of programs with full type hint? 
