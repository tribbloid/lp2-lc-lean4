

import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active

-- System extension, induction rule always cast input into output in either the same system or the most specific system that defined the rule
-- AKA, Typ and Trm are always closed under rules/composition/induction
-- e.g. using STLC rule can cast STLC Typ into STLC Typ, or F Typ into F Typ
-- but using F rule can only cast both STLC/F Typ into F Typ
-- this goes both ways
-- the problem is that theorems are defined for types (including wrapper), not rules
-- Basic (pre)types --

namespace CombineIncompleteMatch

-- SLOP: demonstrate example of combining 2 props into 1

inductive Thing : Type
  | rock : Thing
  | swallow : Thing
  | bat : Thing
  | dog : Thing

def isBird (f : Thing) : Prop :=
  match f with
  | .rock => False
  | .swallow => True
  | .bat => False
  | .dog => False

def isMammal (f : Thing) : Prop :=
  match f with
  | .rock => False
  | .swallow => False
  | .bat => True
  | .dog => True

def isAnimal (f : Thing) : Prop := isBird f ∨ isMammal f

end CombineIncompleteMatch

namespace LeakyRec


inductive Expr0 : Type
  | thing
  | times : Expr0 → Expr0 → Expr0

def recursor0 {motive : Expr0 → Sort u}
  (thing : motive .thing)
  (times : (a b : Expr0) → motive a → motive b → motive (.times a b)) :
  (t : Expr0) → motive t
  | .thing => thing
  | .times a b => times a b (recursor0 thing times a) (recursor0 thing times b)


inductive Expr (F : Type) : Type
  | thing
  | times : Expr F → Expr F → Expr F
  | others: F -> Expr F
  -- can leak to F which can be anything, even the ExprWrapper
  -- when proving a property for Expr F, a continuation lemma has to be provided for .others F.
  -- this shouldn't cover

structure ExprWrapper where
  self: Expr ExprWrapper

def recursor {F : Type} {motive : Expr F → Sort u}
  (thing : motive .thing)
  (times : (a b : Expr F) → motive a → motive b → motive (.times a b))
  (others : (a : F) → motive (.others a)) :
  (t : Expr F) → motive t
  | .thing => thing
  | .times a b => times a b (recursor thing times others a) (recursor thing times others b)
  | .others a => others a

#check @recursor
#check @Expr.rec

section
variable {F: Type} {motive: F -> Sort u} -- technically a higher-kind, don't change it
  -- Case handler type for the known Expr F
  {known: Expr F -> Sort u}

-- def decide
--   (continuation : (e : F) → ((Expr F) ⊕' (motive e)))
--   (known_cases : (e : Expr F) → known e)
--   (e: F)
--   : motive e :=
--   match continuation e with
--   | PSum.inl k =>
--     -- This part is still conceptually incomplete as it depends on how known relates to motive
--     -- but I will fix the syntax error (redundant 'fun e =>' and use 'k' instead of 'known')
--     sorry
--   | PSum.inr proof => proof


-- def leakyRecursorCPS
--   (continuation : (e : F) → ((Expr F) ⊕' (motive e)))
--   (thing : (e : Expr F) → known e)
--   (times : (a b : Expr F) → known a → known b → known (.times a b))
--   : (e : F) → motive e :=
--   fun e =>
--     match continuation e with
--     | PSum.inl k =>
--       -- Again, this is conceptual but fixing syntax/missing cases
--       match k with
--       | .thing => sorry
--       | .times a b => sorry
--       | others a => sorry
--     | PSum.inr proof => proof

end

end LeakyRec

end Lp2lc.Active
