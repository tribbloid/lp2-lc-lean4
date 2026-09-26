# High Priority

## Dual indexing & binding

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

## Parallel Structural Induction? Does it eliminate the need for parametricity axiom?

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
