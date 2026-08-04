# High Priority

## Vacuous proof in __Infer_umbral.lean

- [ ] There is a risk of mixing UIDs from different context to cheat the proof
    - in soundness proof, intermediate term with safety proof can be saved into a context of type `trm2typCtx.Aux0`
    - but Aux0 use the same UID as trm2typCtx, which is also in the environment.
    - as a result, UID can be constructed by trm2typCtx using unproven term, and be submitted to `trm2typCtx.Aux0` to get a vacuous safety proof
    - this should be fixed by:
        - using Aux for safety proof instead of Aux0
        - making AST.ref carrying a subtype of UID that include a dependent Prop to prevent mingling
        - rewriting the safety proof `infer_prove` with new definitions
