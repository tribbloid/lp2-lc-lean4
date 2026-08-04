# High Priority

## Vacuous proof in __Infer_umbral.lean

- [ ] the goal of `infer_prove` is too weak
    - it is only able to prove the consistency of `Trm.infer` and `infer_prove` if both results are Successful (`Outcome.yield .some _`)
    - but `infer_prove` should be a shadow of `infer`: it should also be consistent if the results are `Outcome.outOfFuel` or `Outcome.yield .none`
    - a new `Objective` should be used, in which `sameInfer` is defined independently.

- [ ] There is a risk of mixing UIDs from different context to cheat the proof
    - in soundness proof, intermediate term with safety proof can be saved into a context of type `trm2typCtx.Aux0`
    - but Aux0 use the same UID as trm2typCtx, which is also in the environment.
    - as a result, UID can be constructed by trm2typCtx using unproven term, and be submitted to `trm2typCtx.Aux0` to get a vacuous safety proof
    - this should be fixed by:
        - using Aux for safety proof instead of Aux0
        - making AST.ref carrying a subtype of UID that include a dependent Prop to prevent mingling
        - rewriting the safety proof `infer_prove` with new definitions