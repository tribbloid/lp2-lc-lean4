import Std
import Mathlib.Data.Finset.Basic

import Aesop
import «Lp2lc».Active.Shared
-- import «Lp2lc».Active.Fsub.Def

namespace Lp2lc.Active.Dot

-- Provide a local alias for shared environment well-formedness
-- use shared ok from Lp2lc.Active.Shared

-- [Coq: Dot_top_bot.v line 13]
-- Label for members
structure TypLabel where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

-- [Coq: Dot_top_bot.v line 14]
structure TrmLabel where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

-- WARNING: this formalisation from WadlerFest is very obsolete and should be subsumed by modern definition

-- [Coq: Dot_top_bot.v line 16]
-- label for members
inductive Label : Type where
  | label_typ : TypLabel → Label
  | label_trm : TrmLabel → Label
  deriving Repr, DecidableEq

-- [Coq: Dot_top_bot.v line 20]
inductive Avar : Type where -- variable with a stable path
  | avar_bounded : Nat → Avar -- bound var (de Bruijn serial)
  | avar_free : Var → Avar -- free var
  deriving Repr, DecidableEq

mutual
  -- [Coq: Dot_top_bot.v lines 24-32]
  -- Type
  inductive Typ : Type where
    -- Top/Any
    | typ_top  : Typ
    -- Bottom/Nothing
    | typ_bot  : Typ
    -- Record Piece with 1 member
    -- Intersecting it build a structural type
    -- an empty class/trait is a Record piece with a hidden ClassName type member
    | typ_rcd  : Declaration → Typ
    -- Intersection/Subtype TODO: need Union type
    | typ_and  : (left: Typ) → (right: Typ) → Typ
    -- Dependent selection of type member with a type label
    | typ_sel  : (var: Avar) → (label: TypLabel) → Typ
    -- Self binding / `this.type` in Scala
    -- the only way to use the above `typ_sel` with a de Bruijn serial is within a typ_bnd
    | typ_bnd  : (self: Typ) → Typ
    -- Dependent function (AKA forAll quantifier)
    -- tOut can be a dependent selection, e.g. {x: I => x.DepT}
    -- the typ_all in System F/FSub is half-assed, should rename them
    | typ_function  : (tIn: Typ) → (tOut: Typ) → Typ
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 33]
  inductive Declaration : Type where -- member declaration
    -- Abstract type member with declared upper/lower bounds
    | dec_typ : TypLabel → (upperBound: Typ) → (lowerBound: Typ) → Declaration
    -- Term member with the type assigned to that field/method
    | dec_trm : TrmLabel → Typ → Declaration
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 36]
  -- Term
  inductive Trm : Type where
    -- Variable occurrence, either free or de Bruijn bound
    | trm_var : Avar → Trm
    -- Literal value embedded as a term
    | trm_val : Val → Trm
    -- Selection of a term member from a path (AKA Projection)
    | trm_sel : Avar → TrmLabel → Trm
    -- Function application, both `fn` and `arg` must have a stable path (path or de Bruijn serial)
    -- this is quite different from application in System F/FSub:
    -- due to the lack of dependent typing, there is no need for stable `fn` & `arg` path
    | trm_app : (fn: Avar) → (arg: Avar) → Trm
    -- Let binding, `second` can use the result of `first` with a new de Bruijn serial
    -- it is equivalent to defining a (dependent) function with `second` as the body, then apply to `first`
    -- this equivalence form is used in System F/FSub
    -- but not in this module, as application without stable path is illegal (TODO: we will get rid of it later)
    | trm_let : (first: Trm) → (second: Trm) → Trm
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 42]
  -- Just literal, the only accepted input of atomic normal form (ANF)
  inductive Val : Type where
    -- Object value carrying a self type together with member definitions
    | val_new : Typ → Definitions → Val
    -- Function value with input type annotation and body
    | val_lambda : Typ → Trm → Val
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 46]
  inductive Definition : Type where
    -- Concrete definition assigned to a type member label
    | def_typ : TypLabel → Typ → Definition
    -- Concrete definition assigned to a term member label
    | def_trm : TrmLabel → Trm → Definition
  deriving Repr, DecidableEq

  -- [Coq: Dot_top_bot.v line 49]
  inductive Definitions : Type where
    -- Empty list of member definitions
    | defs_nil : Definitions
    -- Append one member definition to an existing definition list
    | defs_cons : Definitions → Definition → Definitions
  deriving Repr, DecidableEq
end

end Dot
