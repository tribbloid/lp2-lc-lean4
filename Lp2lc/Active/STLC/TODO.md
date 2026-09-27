# High Priority

## Dual indexing

- If you want absolute lambda uniformity/parametricity, stick with De Bruijn serial/cons
- De Bruijn is annoying as each index can map to different entities at different exe frame (build frame also, for dependent functions)
- The core observation: **De Bruijn indices is spatial/hierarchical, frames are temporal**, we need a hashmap-like structure that can handle both
  - binding happen exactly once and is used through out traversal, no more "rekey"/"recarrier".
  - ... due to the totality of KVEquiv, the key has to be generated from the entity
  - ... fortunately, the parallel inductive proof generally don't depends on frame
- Choose 1 of the following
  - inv on frame, key outside .ref, don't rekey lambda body when applying (\`P.inc (c : P.C)\`) <--- require 2-tier KVEquiv
    - frame key can be the outer key or inner key. Proof is easier if frame key is the inner key (soundness doesn't care which entity is used as long as they are all safe to use)
  - inv on binded value, key inside .ref, rekey immediately when applying (\`P.C + Unit\`) <--- Simpler open term description, rekey is verbose in proof
  - something in-between?
- frame is always the outer index in P, de Bruijn is always the inner index in .ref
  - I already have [P.inc](http://P.inc) for advancing de Bruijn, what should happen to the outer index?
  - when the frame advance, it keeps most free vars, how to update the absolute minimal (with delta encoding)?
  - one way to do this is to define frames as a series of delta, each contain exactly 1 de Bruijn index and a fresh \`Val/Typ\`. To avoid circular reference. the Val/Typ is replaced by a equiv key.
    - each var binding generate a new frame, which contains:
      - previous frame
      - frame delta:
        - n: de Bruijn index being updated
        - equiv key of Val/Typ
    - ... the new frame is injected into P : Parameters of the new open AST
    - on traversing AST and get a `.ref m` (where m is the de Bruijn index of an old binding):
      - check if n of the currrent frame delta match m, if so, unbox the equiv key
      - otherwise, go to the previous frame delta.
      - it should never fail: it's easy to prove that the frame series contain 0 .. n, and m < n
    - Implementing eval or compiler should be easy, but can it make proof short?

## Parallel Structural Induction? Does it eliminate the need for parametricity axiom?

I don't think it's worth it, just lift a de Bruijn lambda with subsingleton input into a normal function, then proof it's characteristics on demand. This is more flexible.

The biggest problem for this roadmap is how to steer quickly from Dual Indexing option.

- both eval & infer use AST that can refer to everything
- a single function to produce a bundle of both results:
- since DOT has (mutual) recursion, there is no guarantee that their execution are identical at low level, but they must be related. (this is also a reason that fn type should always carry types of both input & output)

```lean
structure Parallel
  typ: AST.Typ
  inferVal: AST.Val -> AST.Typ -- lambda `val => val.infer`
  relatedSafeVals UIdRefs {x // inferVal x <= typ } -- 1 type can have many values so this has to be a refs
  
  safety: (c : relatedResult.UId) -> (inferResult (relatedResult.get c) <= typ) 
```

- the last member is multiple values related to a type, with their safety proof

The vulnerability of forging Val from Typ UId is thwarted not by using different UId types (UIdEquiv can get/inv Parallel directly), but by **tracking lineage/dependency of construction**

- when constructing val, typ is invisible ()
- when constructing typ, val is invisible (cannot see result of execution iin compiletime)

## [x] Certified AST

## Objective

- Single carrier type for all AST, no more "recarrier"
  - UIdEquiv that uses this carrier must be able to save everything (Val/Typ/Proof etc.)

* eval can only process `Val` , to run (`AST.ref u1).eval` successfully, u1 must be a subtype ({x : P.C // Ev x})
* the 2 parts x and Ev x can be stored in different places, Ev x may be flat
* eval and compile/infer cannot depends on each other
* in addition, the certification can be for the entire AST, instead of each binder .ref, but I don't know how to do it cleanly yet

### Breakpoint compilation

- compilation can process `Val ⊕ Typ` (referring to breakpoint free vars and bounded vars in a subsection respectively)

### Breakpoint compilation is too hard? Start with only closed terms
