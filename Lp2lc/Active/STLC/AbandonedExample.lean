import «Lp2lc».Active.STLC.Def

namespace Lp2lc.Active.SysF.Example

namespace Draft1

theorem stlcProof (F : Type)
  (view : BiMap (STLC.Typ F) F)
  : STLC.Typ F -> SomeBullshitConjecture :=
  sorry

theorem sysFCorollary (F : Type)
  (mk : Typ F -> F)
  (unfold : F -> Typ F)
  : Typ F -> SomeBullshitConjecture
  | .bvar n => bvarLemma F n
  | .fvar x => fvarLemma F x
  | .backbone t =>
    let view : BiMap (STLC.Typ F) F := {
      fwd := fun typ => mk (Typ.backbone typ)
      inv := fun real =>
        let typ := unfold real
        sorry
    }
    stlcProof F view t

end Draft1

namespace Draft2

theorem stlcProof (F : Type)
  (_view : BiMap (STLC.Typ F) F)
  (_v : F)
  : SomeBullshitConjecture :=
  sorry

theorem stlcProofRelaxed (F : Type)
  (mk : STLC.Typ F -> F)
  (unfold : F -> (STLC.Typ F ⊕' SomeBullshitConjecture))
  (v : F)
  : SomeBullshitConjecture :=
    match unfold v with
    | .inl (t : STLC.Typ F) =>
      stlcProof F {
          fwd := mk
          inv := fun _ =>
            t -- THIS SHOULD BE ILLEGAL! function returning t from v is self-referential and should cost fuel
            -- how to associate it with a fuel gauge?
        }
        (mk t)
    | .inr p => p

theorem sysFCorollary (F : Type)
  (mk : BiMap (Typ F) F)
  (v : F)
  : SomeBullshitConjecture :=
    match mk.inv v with
    | .bvar n => bvarLemma F n
    | .fvar x => fvarLemma F x
    | .backbone (t : STLC.Typ F) =>
      let view : BiMap (STLC.Typ F) F := {
        fwd := fun typ => mk.fwd (Typ.backbone typ)
        inv := fun real =>
          match mk.inv real with
          | .backbone t' => t'
          | .bvar _ => t
          | .fvar _ => t
      }
      stlcProof F view v

theorem sysFCorollary2 (F : Type)
  (mk : BiMap (Typ F) F)
  (v : F)
  : SomeBullshitConjecture :=
    let defaultTyp : STLC.Typ F := STLC.Typ.backbone (.all : LC.Typ F)
    let view : BiMap (STLC.Typ F) F := {
      fwd := fun typ => mk.fwd (Typ.backbone typ)
      inv := fun real =>
        match mk.inv real with
        | .backbone t' => t'
        | .bvar _ => defaultTyp
        | .fvar _ => defaultTyp
    }
    stlcProof F view v

end Draft2

end Lp2lc.Active.SysF.Example
