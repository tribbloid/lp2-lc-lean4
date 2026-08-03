import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

namespace SemanticType

def primitiveWhen (proposition : Prop) : Condition I
| .lit _ => proposition
| .lam _ _ => False

def also_primitiveWhen (proposition : Prop) : Condition I := λ v =>
  (∃ e, v = .lit e) ∧ proposition

example : primitiveWhen = also_primitiveWhen := by
  funext proposition value
  cases value <;> simp [primitiveWhen, also_primitiveWhen]

section

variable (proposition : Prop)
variable (evidence : proposition)

example : primitiveWhen proposition (.lit "payload") :=
  evidence

example : ∃ value : Val, primitiveWhen proposition value :=
  ⟨.lit "payload", evidence⟩

example : { value : Val // primitiveWhen proposition value } :=
  ⟨.lit "payload", evidence⟩

example : ¬primitiveWhen proposition Val.idFn := by
  simp [primitiveWhen, Val.idFn]

abbrev AdequateValue (postcondition : Condition I) :=
  { value : Val // postcondition value }

def Hoare (precondition : Prop) (term : Trm)
    (postcondition : Condition I) : Prop :=
  precondition → term.WeakestPre postcondition

def AdequateTerm (term : Trm) (postcondition : Condition I) : Prop :=
  term.WeakestPre postcondition

example :
    Hoare proposition
      (.val (.lit "payload"))
      (primitiveWhen proposition) := by
  intro preconditionEvidence fuel env
  cases fuel with
  | zero => trivial
  | succ fuel => exact preconditionEvidence

example : AdequateValue (primitiveWhen proposition) :=
  ⟨.lit "payload", evidence⟩

-- TODO: where is the evidence
structure TerminatingAdequateTerm (postcondition : Condition I) where
  term : Trm
  evaluates :
    ∀ [@RuntimeEnv I], ∃ fuel : Nat, ∃ result : AdequateValue postcondition,
      term.eval fuel = .yield (some result.1)


example : TerminatingAdequateTerm (primitiveWhen proposition) where
  term := .val (.lit "payload")
  evaluates := by
    intro
    exact ⟨1, ⟨.lit "payload", evidence⟩, rfl⟩

end

-- -- Operational soundness of the logical WP.
-- def WPAdequacy : Prop :=
--   ∀ (term : Trm) (postcondition : Condition I),
--     WeakestPre term postcondition →
--     term.IsSafeBy postcondition

-- Semantic typing for a closed term.
def TypedInSemantic
    (term : Trm) (semanticType : Condition I) : Prop :=
  term.WeakestPre semanticType

-- Adequacy of the logical relation.
def Adequacy : Prop :=
  ∀ (term : Trm) (semanticType : Condition I)
  (_h : TypedInSemantic term semanticType),
    term.IsSafe -- this should be trivial

-- Syntactic typing implies semantic typing.
def Fundamental
    (TypedInSyntax : Trm → AST.Typ I → Prop)
    (denote : AST.Typ I → Condition I) : Prop :=
  ∀ (term : Trm) (type : AST.Typ I),
    TypedInSyntax term type →
    TypedInSemantic term (denote type) -- real compilation happens here

end SemanticType

end Tests.STLC.Sanity
