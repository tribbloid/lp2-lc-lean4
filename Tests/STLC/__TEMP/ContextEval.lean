import Tests.STLC.TrmDemo

namespace Tests.STLC.ContextEval

open Lp2lc.Active.Util Lp2lc.Active.STLC

/-- Attaches a context to any indexed syntax family, without inspecting its constructors. -/
structure InContext {Index : Type} (Syntax : Index → Label → Type 2) (EnvId : Type) (label : Label) where
  index : Index
  env : EnvId
  ast : Syntax index label

/-- Canonical receipts identify closures and immutable environments independently of lexical slots. -/
structure Runtime (P : Parameters) where
  ValueId : Type
  EnvId : Type
  values : KVRefs ValueId (InContext (@AST P) EnvId .val)
  valueEquiv : KVEquiv values
  envs : KVRefs EnvId (List (P.C × ValueId))
  envEquiv : KVEquiv envs

section variable {P : Parameters} [DecidableEq P.C] (runtime : Runtime P)

/-- Evaluates an existing syntax node in its captured environment. -/
private def evalOpen (self : InContext (@AST P) runtime.EnvId .trm) :
    RecOpt (InContext (@AST P) runtime.EnvId .val)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | ⟨index, env, .val value⟩ => .yield (some ⟨index, env, value⟩)
    | ⟨index, env, .apply fnTerm arg⟩ =>
      let anf := (evalOpen ⟨index, env, fnTerm⟩ fuel,
        evalOpen ⟨index, env, arg⟩ fuel)
      match anf with
      | (.yield (some ⟨index, captured, .fn _ body⟩), .yield (some arg)) =>
        let receipt := runtime.valueEquiv.inv arg
        let extended := runtime.envEquiv.inv ((index, receipt) :: runtime.envs.get captured)
        evalOpen ⟨({P with index}).Next.index, extended, body.apply .only⟩ fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | ⟨_, env, @AST.ref _ index _⟩ =>
      .yield (((runtime.envs.get env).find? (λ entry => decide (entry.1 = index))).map
        (λ entry => runtime.values.get entry.2))

/-- The public entry point starts a closed source term with the empty environment. -/
def eval (self : AST.Trm (P := P) root) : RecOpt (InContext (@AST P) runtime.EnvId .val) :=
  evalOpen runtime ⟨root, runtime.envEquiv.inv [], self⟩

end

section eval

open Sanity Sanity.Symbolic

deriving instance DecidableEq for DemoCarrier

variable (runtime : Runtime I)

example : eval runtime Trm.primitiveIdFnOnFalse 2 =
    .yield (some ⟨.root, runtime.envEquiv.inv [], .lit bFalse⟩) := by
  simp [eval, evalOpen, Trm.primitiveIdFnOnFalse, Trm.primitiveIdFn, Trm.vFalse, Binder.apply]

example : eval runtime (.apply Trm.primitiveIdFn Trm.vTrue) 2 =
    .yield (some ⟨.root, runtime.envEquiv.inv [], .lit bTrue⟩) := by
  simp [eval, evalOpen, Trm.primitiveIdFn, Trm.vTrue, Binder.apply]

example : eval runtime Trm.get1stOnTuple 3 =
    .yield (some ⟨.root, runtime.envEquiv.inv [], .lit bFalse⟩) := by
  simp [eval, evalOpen, Trm.get1stOnTuple, Trm.get1st, Trm.vFalse, Trm.vTrue, Binder.apply]

example : eval runtime Trm.get2ndOnTuple 3 =
    .yield (some ⟨.root, runtime.envEquiv.inv [], .lit bTrue⟩) := by
  simp [eval, evalOpen, Trm.get2ndOnTuple, Trm.get2nd, Trm.vFalse, Trm.vTrue, Binder.apply]

example : eval runtime Trm.Malformed.idFnOnFalse2 3 =
    .yield (some ⟨.root, runtime.envEquiv.inv [], .lit bFalse⟩) := by
  simp [eval, evalOpen, Trm.Malformed.idFnOnFalse2, Trm.Malformed.applyIdFnOnItself,
    Trm.primitiveIdFn, Trm.vFalse, Binder.apply]

example : eval runtime Trm.Malformed.primitiveApply 2 = .yield none := by
  simp [eval, evalOpen, Trm.Malformed.primitiveApply, Trm.vFalse, Trm.vTrue]

example : eval runtime Trm.primitiveIdFnOnFalse 1 = .outOfFuel := by
  simp [eval, evalOpen, Trm.primitiveIdFnOnFalse]

example (value : InContext (@AST I) runtime.EnvId .val) :
    evalOpen runtime
      ⟨.extended, runtime.envEquiv.inv [(.root, runtime.valueEquiv.inv value)],
        AST.ref (P := I) (c := .root) .only⟩ 1 =
      .yield (some value) := by
  simp [evalOpen]

example : evalOpen runtime
    ⟨.extended, runtime.envEquiv.inv [], AST.ref (P := I) (c := .root) .only⟩ 1 = .yield none := by
  simp [evalOpen]

end eval

section serial

abbrev Serial : Parameters := { C := Nat, B := Nat, inc := Nat.succ }

example (runtime : Runtime Serial) :
    eval runtime (root := 0) (.apply (.val (.fn .TLit (.mk (λ input => .ref input)))) (.val (.lit 7))) 2 =
      .yield (some ⟨0, runtime.envEquiv.inv [], .lit 7⟩) := by
  simp [eval, evalOpen, Binder.apply]

-- With successor indexing, an outer slot produces a term at depth 1, not at depth 2.
example : True := by
  fail_if_success
    have _outer : AST.Trm (P := Serial) 2 := AST.ref (P := Serial) (c := 0) .only
  trivial

end serial

/-- Retaining the key and its lookup equation makes any lookup bijective to located payloads. -/
def located {K} {V : Type 2} (refs : KVRefs K V) :
    KVRefs K ((key : K) × {value : V // refs.get key = value}) :=
  ⟨λ key => ⟨key, refs.get key, rfl⟩⟩

def locatedEquiv {K} {V : Type 2} (refs : KVRefs K V) : KVEquiv (located refs) where
  inv value := value.1
  rightInv value := by
    rcases value with ⟨key, value, equality⟩
    cases equality
    rfl
  leftInv _ := rfl

end Tests.STLC.ContextEval
