# High Priority

## Dual indexing

- If you want absolute lambda uniformity/parametricity, stick with De Bruijn serial/cons
- De Bruijn is awkward because each index can map to different entities in different execution or build frames,
      including dependent functions.
- The core observation: **De Bruijn indices are spatial/hierarchical, while frames are temporal**. We need a
      hashmap-like structure that can handle both.
    - binding happens exactly once and is used throughout traversal, with no more "rekey"/"recarrier".
    - ... due to the totality of KVEquiv, the key has to be generated from the entity
    - ... fortunately, the parallel inductive proof generally does not depend on the frame
- Choose one of the following:
    - inv on frame, key outside .ref, don't rekey lambda body when applying (`P.Next`); requires 2-tier KVEquiv
        - The frame key can be the outer or inner key. Proof is easier with the inner key; soundness only requires
      that every entity used is safe.
    - inv on bound value, key inside .ref, rekey immediately when applying (`P.C + Unit`); this gives a simpler
      open term description, but rekeying is verbose in proofs.
    - Something in between?
- The frame is always the outer index in P, while De Bruijn is always the inner index in `.ref`.
    - `P.Next` advances the lexical index; what should happen to the outer index?
    - When the frame advances, it keeps most free variables; how can it update the minimum needed (with delta encoding)?
    - One way is to define frames as a series of deltas, each containing one De Bruijn index and a fresh
      `Val`/`Typ`. To avoid a circular reference, an equivalence key replaces the `Val`/`Typ`.
        - Each variable binding generates a new frame containing:
            - previous frame
            - frame delta:
                - n: de Bruijn index being updated
                - equiv key of Val/Typ
        - ... the new frame is injected into `P : Parameters` of the new open AST
        - On traversing AST and reaching a `.ref m` (where m is the De Bruijn index of an old binding):
            - check whether n of the current frame delta matches m; if so, unbox the equivalence key
            - otherwise, go to the previous frame delta.
            - It should never fail: the frame series contains 0 .. n, and m < n.
        - Implementing evaluation or a compiler should be easy, but can the proof be short?

## Parallel Structural Induction? Does it eliminate the need for parametricity axiom?

I don't think it's worth it. Lift a De Bruijn lambda with subsingleton input into a normal function, then prove
its characteristics on demand. This is more flexible.

The biggest problem for this roadmap is how to move quickly from the dual indexing option.

- Both evaluation and inference use AST nodes that can refer to everything.
- A single function produces a bundle of both results:
- Since DOT has mutual recursion, there is no guarantee that the executions are identical at a low level, but
      they must be related. This is also why the function type should carry both input and output types.

```lean
structure Parallel
  typ: AST.Typ
  inferVal: AST.Val -> AST.Typ -- lambda `val => val.infer`
  relatedSafeVals UIdRefs {x // inferVal x <= typ } -- 1 type can have many values so this has to be a refs
  
  safety: (c : relatedResult.UId) -> (inferResult (relatedResult.get c) <= typ) 
```

- The last member holds multiple values related to a type, with their safety proofs.

Forging `Val` from a `Typ` UId is prevented by **tracking the lineage/dependency of construction**. Distinct UId
types alone do not prevent it because `KVEquiv` can get/invert `Parallel` directly.

- When constructing a value, its type is invisible.
- When constructing a type, its value is invisible (the result of execution is unavailable at compile time).

## [x] Certified AST

## Objective

- A single carrier type for all AST nodes, with no more "recarrier".
    - `KVEquiv` using this carrier must be able to save everything (`Val`, `Typ`, proofs, and so on).

- Evaluation can only process `Val`; to evaluate `AST.ref u1` successfully, u1 must be a subtype
      (`{x : P.C // Ev x}`).
- The two parts, x and Ev x, can be stored in different places; Ev x may be flat.
- Evaluation and compilation/inference cannot depend on each other.
- Certification can cover the entire AST instead of each binder `.ref`, but I don't know how to do it cleanly yet.

### Breakpoint compilation

- Compilation can process `Val ⊕ Typ` (breakpoint free variables and bound variables in a subsection, respectively).

### Breakpoint compilation is too hard? Start with only closed terms
