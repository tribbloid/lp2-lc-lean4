import «Lp2lc».Active.STLC.Serial.__Infer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.InferRefutation

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity
open Lp2lc.Active.Util.Indices.SerialProxy (only)

section infer

private def knownTypes (index : Nat) : Option ((context : Nat) × Typ context) :=
  if index = 0 then some ⟨5, .TFn .TLit (.TFn .TLit .TLit)⟩
  else if index = 1 then some ⟨7, .TLit⟩ else none

private def higherOrderArg : Trm 0 :=
  .val (.fn (.TFn .TLit .TLit) (.mk (λ fn =>
    .apply (.ref fn .same) (.val (.lit "arg")))))

private def ghostRef : Trm 0 :=
  .val (.fn .TLit (.mk (λ _ => .ref only (.lower .same))))

private def missingDeepInputRef : Trm :=
  .val (.fn (.TFn .TLit (.TFn .TLit .TLit))
    (.mk (λ _ => .ref only (.lower (.lower .same)))))

/-- but is expected to have type Trm 8 -/
#guard_msgs (error, drop info, whitespace := lax, substring := true) in
#check AST.infer (n := 8) (.TLit : Typ 8)

/-- but is expected to have type Trm 8 -/
#guard_msgs (error, drop info, whitespace := lax, substring := true) in
#check AST.infer (n := 8) (.lit "false" : Val 8)

example : AST.infer Trm.FreeCapture.directRef (λ _ => some ⟨8, .TLit⟩) 0 = .outOfFuel := by rfl
example : AST.infer Trm.FreeCapture.directRef (λ _ => some ⟨8, .TLit⟩) 1 = .outOfFuel := by rfl
example : AST.infer Trm.FreeCapture.directRef (λ _ => some ⟨8, .TLit⟩) 2 =
    .yield (some .TLit) := by rfl
example : AST.infer Trm.FreeCapture.directRef (λ _ => some ⟨8, .TFn .TLit .TLit⟩) 2 =
    .outOfFuel := by rfl
example : AST.infer Trm.FreeCapture.directRef (λ _ => some ⟨8, .TFn .TLit .TLit⟩) 3 =
    .yield (some (.TFn .TLit .TLit)) := by rfl
example : AST.infer (.val (.lit "false") : Trm 8) (λ _ => none) 0 = .outOfFuel := by rfl
example : AST.infer (.val (.lit "false") : Trm 8) (λ _ => none) 1 = .yield (some .TLit) := by rfl

example : AST.infer Trm.vFalse (λ _ => none) 0 = .outOfFuel := by rfl
example : AST.infer Trm.vFalse (λ _ => none) 1 = .yield (some .TLit) := by rfl
example : AST.infer Trm.vFalse knownTypes 1 = AST.infer Trm.vFalse knownTypes 9 := by rfl
example : AST.infer Trm.vTrue (λ _ => none) 1 = .yield (some .TLit) := by rfl

example : AST.infer Trm.FreeCapture.directRef (λ _ => none) 1 = .yield none := by rfl
example : AST.infer Trm.FreeCapture.directRef (λ _ => none) 1 =
    AST.infer Trm.FreeCapture.directRef (λ _ => none) 9 := by rfl
example : AST.infer Trm.FreeCapture.directRef knownTypes 3 = .outOfFuel := by rfl
example : AST.infer Trm.FreeCapture.directRef knownTypes 4 =
    .yield (some (.TFn .TLit (.TFn .TLit .TLit))) := by rfl
example : AST.infer Trm.FreeCapture.directRef knownTypes 4 =
    AST.infer Trm.FreeCapture.directRef knownTypes 9 := by rfl
example : AST.infer
    (.ref (P' := { B := String, I := .Serial, index := 1 }) .only (.lower (.lower .same)) : Trm 3)
    knownTypes 2 =
    .yield (some .TLit) := by rfl

example : AST.infer Trm.primitiveIdFn (λ _ => none) 3 = .yield (some (.TFn .TLit .TLit)) := by rfl
example : AST.infer Trm.primitiveIdFn (λ _ => none) 2 = .outOfFuel := by rfl
example : AST.infer Trm.primitiveIdFn (λ _ => some ⟨0, .TFn .TLit .TLit⟩) 3 =
    .yield (some (.TFn .TLit .TLit)) := by rfl
example : AST.infer Trm.primitiveIdFn knownTypes 3 = AST.infer Trm.primitiveIdFn knownTypes 9 := by rfl
example : AST.infer (.val Val.idFn) knownTypes 3 = AST.infer (.val Val.idFn) knownTypes 9 := by rfl
example : AST.infer Trm.primitiveIdFnOnFalse (λ _ => none) 3 = .outOfFuel := by rfl
example : AST.infer Trm.primitiveIdFnOnFalse (λ _ => none) 4 = .yield (some .TLit) := by rfl
example : AST.infer Trm.primitiveIdFnOnFalse knownTypes 4 =
    AST.infer Trm.primitiveIdFnOnFalse knownTypes 9 := by rfl

example : AST.infer Trm.get1st (λ _ => none) 3 = .outOfFuel := by rfl
example : AST.infer Trm.get1st (λ _ => none) 4 = .yield (some (.TFn .TLit (.TFn .TLit .TLit))) := by rfl
example : AST.infer Trm.get2nd (λ _ => none) 4 = .yield (some (.TFn .TLit (.TFn .TLit .TLit))) := by rfl
example : AST.infer Trm.get1stOnTuple (λ _ => none) 5 = .outOfFuel := by rfl
example : AST.infer Trm.get1stOnTuple (λ _ => none) 6 = .yield (some .TLit) := by rfl
example : AST.infer Trm.get2ndOnTuple (λ _ => none) 6 = .yield (some .TLit) := by rfl
example : AST.infer Trm.get1st knownTypes 4 = AST.infer Trm.get1st knownTypes 9 := by rfl
example : AST.infer Trm.get2nd knownTypes 4 = AST.infer Trm.get2nd knownTypes 9 := by rfl
example : AST.infer Trm.get1stOnTuple knownTypes 6 = AST.infer Trm.get1stOnTuple knownTypes 9 := by rfl
example : AST.infer Trm.get2ndOnTuple knownTypes 6 = AST.infer Trm.get2ndOnTuple knownTypes 9 := by rfl
example : AST.infer Trm.primitiveTrueFn (λ _ => none) 2 =
    .yield (some (.TFn .TLit .TLit)) := by rfl
example : AST.infer Trm.primitiveTrueFnOnFalse (λ _ => none) 3 = .yield (some .TLit) := by rfl
example : AST.infer Trm.TypeHinted.hintedFalse (λ _ => none) 1 = .yield (some .TLit) := by rfl
example : AST.infer Trm.TypeHinted.hintedIdFn (λ _ => none) 3 =
    .yield (some (.TFn .TLit .TLit)) := by rfl
example : AST.infer Trm.TypeHinted.hintedIdFnOnFalse (λ _ => none) 4 = .yield (some .TLit) := by rfl

example : AST.infer (.apply Trm.FreeCapture.directRef Trm.vFalse) knownTypes 5 =
    .yield (some (.TFn .TLit .TLit)) := by rfl
example : AST.infer (.apply Trm.FreeCapture.directRef Trm.vFalse) knownTypes 5 =
    AST.infer (.apply Trm.FreeCapture.directRef Trm.vFalse) knownTypes 9 := by rfl
example : AST.infer Trm.FreeCapture.capturedRef knownTypes 5 =
    .yield (some (.TFn .TLit (.TFn .TLit (.TFn .TLit .TLit)))) := by rfl
example : AST.infer Trm.FreeCapture.capturedRef knownTypes 5 =
    AST.infer Trm.FreeCapture.capturedRef knownTypes 9 := by rfl
example : AST.infer Trm.FreeCapture.capturedRefOnFalse (λ _ => some ⟨0, .TLit⟩) 4 =
    .yield (some .TLit) := by rfl
example : AST.infer higherOrderArg (λ _ => none) 4 = .outOfFuel := by rfl
example : AST.infer higherOrderArg (λ _ => none) 5 =
    .yield (some (.TFn (.TFn .TLit .TLit) .TLit)) := by rfl
example : AST.infer (.apply higherOrderArg Trm.primitiveIdFn) knownTypes 6 = .yield (some .TLit) := by rfl
example : AST.infer (.apply higherOrderArg Trm.primitiveIdFn) knownTypes 6 =
    AST.infer (.apply higherOrderArg Trm.primitiveIdFn) knownTypes 9 := by rfl

example : AST.infer missingDeepInputRef (λ _ => none) 3 = .outOfFuel := by rfl
example : AST.infer missingDeepInputRef (λ _ => none) 4 = .yield none := by rfl
example : AST.infer missingDeepInputRef (λ _ => none) 4 =
    AST.infer missingDeepInputRef (λ _ => none) 9 := by rfl

example : AST.infer ghostRef knownTypes 1 = .outOfFuel := by rfl
example : AST.infer ghostRef knownTypes 2 = .yield none := by rfl
example : AST.infer ghostRef knownTypes 2 = AST.infer ghostRef knownTypes 9 := by rfl
example : AST.infer Trm.Malformed.applyIdFnOnItself knownTypes 4 = .yield none := by rfl
example : AST.infer Trm.Malformed.applyIdFnOnItself knownTypes 4 =
    AST.infer Trm.Malformed.applyIdFnOnItself knownTypes 9 := by rfl
example : AST.infer Trm.Malformed.primitiveApply knownTypes 2 = .yield none := by rfl
example : AST.infer Trm.Malformed.primitiveApply knownTypes 2 =
    AST.infer Trm.Malformed.primitiveApply knownTypes 9 := by rfl
example : AST.infer Trm.Malformed.idFnOnFalse2 knownTypes 5 = .yield none := by rfl
example : AST.infer Trm.Malformed.apply1 knownTypes 5 = .yield none := by rfl

example : AST.infer (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) knownTypes 2 = .outOfFuel := by rfl
example : AST.infer (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) knownTypes 5 = .yield none := by rfl
example : AST.infer (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) knownTypes 5 =
    AST.infer (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) knownTypes 9 := by rfl

end infer

end Tests.STLC.InferRefutation
