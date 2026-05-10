import «Lp2lc».Active.DTLC.Def

namespace Lp2lc.Active

namespace DTLC

open Util

namespace Runtime

/-- Runtime semantic values produced by typed compilation. -/
inductive SemanticVal (I : Index) : Type where
| primitive (repr : ByteCode)
| fn (body : (arg : I) -> Trm I)

/-- Converts a runtime semantic value back to the source value needed by HOAS bodies. -/
def SemanticVal.to_val {I : Index} (value : SemanticVal I) : Val I :=
  match value with
  | .primitive repr => .primitive repr
  | .fn body => .fn body

/-- Compiled runtime artifact paired with the annotation it was checked against. -/
structure Compiled (I : Index) : Type where
  type_annotation : Typ I
  value : SemanticVal I

/-- Runtime execution result for a compiled artifact. -/
inductive ExecResult (I : Index) : Type where
| success (value : SemanticVal I)
| out_of_fuel

/-- Runtime compilation result for an annotated source term. -/
inductive CompileResult (I : Index) : Type where
| success (compiled : Compiled I)
| type_error
| out_of_fuel

/-- Tests whether a runtime value has the shape requested by a type annotation. -/
@[simp] private def SemanticVal.matches_type {I : Index} (value : SemanticVal I)
    (type_annotation : Typ I) : Bool :=
  match type_annotation with
  | .primitive =>
    match value with
    | .primitive _ => true
    | .fn _ => false
  | .depFn _ _ =>
    match value with
    | .primitive _ => false
    | .fn _ => true
  | .top => true

/-- Interprets a source value as a runtime semantic value. -/
@[simp] private def SemanticVal.of_val {I : Index} (value : Val I) : SemanticVal I :=
  match value with
  | .primitive repr => .primitive repr
  | .fn body => .fn body

/-- Compiles a source value after checking its annotation shape. -/
@[simp] private def compile_val {I : Index} (value : Val I)
    (type_annotation : Typ I) : CompileResult I :=
  let runtime_value := SemanticVal.of_val value
  if runtime_value.matches_type type_annotation then
    .success { type_annotation := type_annotation, value := runtime_value }
  else
    .type_error

/-- Executes a compiled artifact; only fuel exhaustion can stop execution. -/
def Compiled.run {I : Index} (compiled : Compiled I) (fuel : Nat) : ExecResult I :=
  match fuel with
  | 0 => .out_of_fuel
  | _ + 1 => .success compiled.value

mutual

/-- Compiles an annotated source term into a runtime semantic value. -/
def compile {I : Index} [FBound I] (trm : Trm I) (fuel : Nat)
    (type_annotation : Typ I) : CompileResult I :=
  match fuel with
  | 0 => .out_of_fuel
  | fuel + 1 =>
    match trm with
    | .val value => compile_val value type_annotation
    | .depApply fn arg =>
      match compile fn fuel .top, compile arg fuel .top with
      | .success compiled_fn, .success compiled_arg =>
        compiled_fn.apply compiled_arg fuel type_annotation
      | .out_of_fuel, _ => .out_of_fuel
      | _, .out_of_fuel => .out_of_fuel
      | _, _ => .type_error

/-- Applies a compiled function to a compiled argument through the source HOAS boundary. -/
def Compiled.apply {I : Index} [FBound I] (compiled_fn : Compiled I)
    (compiled_arg : Compiled I) (fuel : Nat) (type_annotation : Typ I) : CompileResult I :=
  match fuel with
  | 0 => .out_of_fuel
  | fuel + 1 =>
    match compiled_fn.value with
    | .primitive _ => .type_error
    | .fn body =>
      match compiled_fn.type_annotation with
      | .primitive => .type_error
      | .depFn input_type _ =>
        if compiled_arg.value.matches_type input_type then
          compile (body (FBound.fwd compiled_arg.value.to_val)) fuel type_annotation
        else
          .type_error
      | .top =>
        compile (body (FBound.fwd compiled_arg.value.to_val)) fuel type_annotation

end

end Runtime

end DTLC

end Lp2lc.Active
