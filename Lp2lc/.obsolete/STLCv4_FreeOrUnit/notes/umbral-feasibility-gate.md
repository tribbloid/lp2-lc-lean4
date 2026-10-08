# Umbral feasibility gate: infeasible under the current guardrails

Date: 2026-08-23, after commits b4e7594..bb7e4a6 (separated free/bound receipt carriers, pure PHOAS).

## Gate question

Can runtime-`B` and build-`B` instantiations of one source term be related constructively from the AST and the existing environments (`ExeRefs`, `ExeEnv`, `BuildEnv`), so that `Umbral.infer` can be discharged without a new assumption?

## Verdict

Infeasible. Discharging `Umbral.infer` would require relating the behaviour of one polymorphic term at two different bound-carrier instantiations, which needs a relational-parametricity (∀-extensionality) principle for the lambda body. Lean does not supply it and the task guardrail forbids adding it ("no new axiom ... no parametricity witness"). Per TODO step 6's escape clause the theorem is reported infeasible; step 7 was not attempted.

## Argument

1. `Safety trm t2` compares `(trm (B := refs.uid2val.UId)).eval` against `(trm (B := build.uid2typ.UId)).infer` of the same source term.
2. A polymorphic term can only be inspected after fixing one carrier; structural induction therefore fixes a single carrier, while the two phases run at different carriers. No induction hypothesis transfers between the instantiations.
3. The `.lam` case makes the gap precise: evaluation substitutes the minted runtime receipt into `body : B → Trm P(B)` while inference substitutes the minted type receipt; equating the two substituted bodies across carriers is exactly parametricity for `body`.
4. Necessary condition checked: no lawful closed counterexample exists in the new representation. The adversarial review (2026-08-23) failed to break the design across all mandated vectors; the retired `binderIdentityCounterexample` is unrepresentable because a body argument is a `P.B` receipt with no route from `P.F`. As the gate states, this is necessary but not sufficient.
5. Corroboration: the adversarial artifact shows phase divergence becomes expressible exactly when an attacker assumes carrier sharing (`build.uid2typ.UId = refs.uid2val.UId`); the soundness margin of the composition lives in the uniformity of polymorphic terms, which is not constructively accessible.

## Final audits (same date)

- Assumption/capability audit: AUDIT PASS. Inventory unchanged versus baseline (`#print axioms`: eval [propext], infer [propext, Quot.sound], monotone theorems ditto, Umbral.infer [sorryAx] scaffold); sole class change is `Parameters.C` → `Parameters.F`/`Parameters.B`; no new axiom, abstract field, or capability.
- Adversarial safety audit: ADVERSARIAL FAIL TO BREAK; positive controls (nested binders, free capture) exercised.
