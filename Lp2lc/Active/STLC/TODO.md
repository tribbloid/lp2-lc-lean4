# STLC TODO

- [ ] Implement `AST.Trm.compile` so every mandatory `Trm.val` hint is translated to a semantic condition and checked against the wrapped value. The current `sorry` branches do not yet reject mismatched hints, malformed applications, or invalid references.
- [x] Remove `AST.Val.compute`; a host function from `I.Data` to `Trm` is more expressive than the core simply typed lambda calculus.
- [x] Reclassify `Trm.applyidFnOnItself` and `Trm.idFnOnFalse2` as malformed typing examples. `primitiveIdFn` is annotated as `.fn .primitive .primitive`, so passing `primitiveIdFn` itself as its primitive argument is not typable in STLC even though the untyped evaluator can reduce it.
- [x] Use the fixed-typed `primitiveIdFn` examples from `Tests/Example/TrmDemo.scala` in `Tests/STLC/TrmDemo.lean`; the dependent `idFn` examples are not supported by STLC.


# Need a better FBound system to sync UIDs between terms, types and values

Options:

- multi-part UID: first part is always isomorphic to the term, second part is a unique identifier for the type or value.
- single-part UID: only isomorphic to the term.

- During compilation & proving, the FBound must save both typing result and safety proof to a fn term (specifically to its binder variable).
- During evaluation, when FBound save a binded value:
	1. fnBody (uidInEval) == fnBody (uidInCompile)
	  since fnBody only produce a new AST, it doesn't even matter if both uid are identical, and eval will need a second part of the index to compute.
	2. load (uidInEval).infer <= load (uidInCompile)
      AKA safety proof of binded variables.

## Advantage of single-part UID

uidInEval == uidInCompile

(1) become trivial

loading value & eval fn output takes an extra (part 2) instance uid.
	- this makes runtime FBound 2 stage: (UID) -> ((instanceUID) -> value , term)

(2) ... the proof has to be from ProvingEnv:
	- ProvingEnv has a shadow FBound mimicking the runtime FBound.
	- whenever `v = term.eval` is called recursively, term.infer is called in the shadow.
	- when `v` is saved in runtime FBound, the proof that v.infer is safe is saved into ProvingEnv FBound in the shadow
	- value returned by eval will be tagged by the type the original expression infers to
	- only tagged value can be saved into runtime FBound

## Formalising the above architecture

```
def UID1 := I

def UID2 := I

CompilerEnv : UID1 -> Typ I

RuntimeEnv : UID1 -> (UID2 -> Val I)

def InhabitingEv : Trm I -> Typ I

def Adequacy : InferenceLemma -> Safety

ProvingEnv : UID1 -> ((UID2 -> InhabitingEv), Adequacy)
```