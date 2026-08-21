# Confirmed defects

## Transport hell among all theorems that relies on UIdEquiv

### Here is a list of all the transport:

- ExeEnv -> BuildEnv
  - can no longer save value, can save type
  - can convert term by simple upcast
    - references in term become free variables
- BuildEnv -> ExeEnv
  - the opposite
  - can only convert closed term, open term with type reference will become broken
- compatible Env also have compatible ExeParameters
  - but this info will be lost in transport hell

### For AI proving, extra requirement may interfere with optimal design:

- ExeEnv & BuildEnv should not be a depend type of each other
  - doing so will allow each Env to construct each other using from `match`, enabling a cheater compiler (e.g. eval in compile-time)
- UIdView and UIdEquiv should never share their UId types
  - doing so will allow forged construction, as UIdView\.get is a total function

### Doctrine of an optimal design:

- UIdEquiv type should depend on UIdView, `x: UIDEquiv V` and `v : V` always share the same UId (But don't drop the subtyping/coercion)
- ExeEnv and BuildEnv should both depends on an `EnvCore`, such that consistency of `D` and `UIDView` is enforced by its member, but both Env cannot construct each other
  - `ExeParameter` and `BuildParameters` can be members of `EnvCore` directly.
