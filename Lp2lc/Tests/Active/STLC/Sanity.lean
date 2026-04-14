import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC.Tests

open Lp2lc.Active.STLC

namespace Trm

def trm1 (Index : Type) : Trm Index :=
 .literal ""

def trm2 : ClosedTrm := trm1 -- eta-expansion happens automatically

def trm3 (Index : Type) : Trm Index :=
 trm2 Index

end Trm

namespace Typ

/--
```scala
type Base = String
val lit: Base = "hello"
```
-/
def literal_type : Typ :=
  TypProto.base

#guard
  let _ : literal_type = (TypProto.base : Typ) := rfl
  true

/--
```scala
type Base = String
val id: Base => Base = x => x
```
-/
def identity_type : Typ :=
  TypProto.arrow TypProto.base TypProto.base

#guard
  let _ : identity_type = TypProto.arrow TypProto.base TypProto.base := rfl
  true

/--
```scala
type Base = String
val const: Base => Base => Base = x => _ => x
```
-/
def const_type : Typ :=
  TypProto.arrow TypProto.base (TypProto.arrow TypProto.base TypProto.base)

#guard
  let _ : const_type = TypProto.arrow TypProto.base (TypProto.arrow TypProto.base TypProto.base) := rfl
  true

end Typ

namespace ClosedTrm

/--
```scala
type Base = String
val lit: Base = "hello"
```
-/
def literal : ClosedTrm :=
  fun _ => .literal "\"hello\""

#guard
  let _ : literal.Typed = Trm.literal "\"hello\"" := rfl
  true

/--
```scala
type Base = String
val id: Base => Base = x => x
```
-/
def identity : ClosedTrm :=
  fun _ =>
    .monoFunction
      (fun argument => .var argument .base)
      .base

#guard
  let _ :
      identity.Typed =
        Trm.monoFunction
          (fun argument => Trm.var argument TypProto.base)
          TypProto.base := rfl
  true

/--
```scala
type Base = String
val const: Base => Base => Base = x => _ => x
```
-/
def constFn : ClosedTrm :=
  fun _ =>
    .monoFunction
      (fun left =>
        .monoFunction
          (fun _ => .var left .base)
          .base)
      .base

#guard
  let _ :
      constFn.Typed =
        Trm.monoFunction
          (fun left =>
            Trm.monoFunction
              (fun _ => Trm.var left TypProto.base)
              TypProto.base)
          TypProto.base := rfl
  true

/--
```scala
type Base = String
((x: Base) => x)("hello")
```
-/
def identityApplication : ClosedTrm :=
  fun _ =>
    .apply
      (.monoFunction
        (fun argument => .var argument .base)
        .base)
      (.literal "\"hello\"")

#guard
  let _ :
      identityApplication.Typed =
        Trm.apply
          (Trm.monoFunction
            (fun argument => Trm.var argument TypProto.base)
            TypProto.base)
          (Trm.literal "\"hello\"") := rfl
  true

end ClosedTrm

end Tests
