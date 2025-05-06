
section FSubStr

  /- Representation of pre-types -/
  inductive Typ : Type where
    | typ_top   : Typ
    | typ_bvar  : Nat → Typ
    | typ_fvar  : String → Typ
    | typ_arrow : Typ → Typ → Typ
    | typ_all   : Typ → Typ → Typ

  /- Representation of pre-terms -/
  inductive Trm : Type where
    | trm_bvar : Nat → Trm
    | trm_fvar : String → Trm
    | trm_abs  : Typ → Trm → Trm
    | trm_app  : Trm → Trm → Trm
    | trm_tabs : Typ → Trm → Trm
    | trm_tapp : Trm → Typ → Trm

end FSubStr
