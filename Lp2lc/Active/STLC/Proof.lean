import Mathlib.Tactic
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.Def

/-!
This file proves soundness for simply typed lambda calculus by interpreting
terms with a step-indexed logical relation. The step index is the fuel used to
reason about functions recursively: a function is safe for `fuel` when, for
any `lessFuel ≤ fuel`, it sends semantically safe inputs to outputs that
stay safe one guarded step later.

All docstrings use short (under 5 lines) of Scala code as demonstrations.
-/

namespace Lp2lc.Active.STLC

/--
Step-indexed logical relation describing semantically well-behaved values.
-/
def Semantics (type : Ty) (data : type.Denotation) (fuel : Nat) : Prop :=
  match type with
  | .base => True
  | .arrow input output =>
      let fn := data
      ∀ lessFuel, lessFuel ≤ fuel →
        ∀ (vIn : input.Denotation), Semantics input vIn lessFuel →
          Later (Semantics output (fn vIn) lessFuel)

lemma Semantics.monotone {fuel lessFuel : Nat} (lessEv : lessFuel ≤ fuel)
    {value : type.Denotation} :
    Semantics type value fuel → Semantics type value lessFuel := by
  induction type generalizing lessFuel fuel with
  | base =>
      intro valueSemantics
      simp [Semantics] at valueSemantics ⊢
  | arrow input output _ _ =>
      intro functionSemantics
      have functionSemantics' :
          ∀ testFuel, testFuel ≤ fuel →
            ∀ testValue, Semantics input testValue testFuel →
              Later (Semantics output (value testValue) testFuel) := by
        simpa [Semantics] using functionSemantics
      change
        ∀ testFuel, testFuel ≤ lessFuel →
          ∀ testValue, Semantics input testValue testFuel →
            Later (Semantics output (value testValue) testFuel)
      intro testFuel testBound testValue testSemantics
      exact functionSemantics' testFuel (Nat.le_trans testBound lessEv) testValue testSemantics

def REPLSemantics {TermVar : Type} [DecidableEq TermVar]
    (repl : REPL TermVar) (fuel : Nat) : Prop :=
  ∀ (name : TermVar) (type : Ty) (binding : repl.env.get name = some type),
    Semantics type (repl.varLookup name type binding) fuel

lemma REPLSemantics.monotone {TermVar : Type} [DecidableEq TermVar]
    {repl : REPL TermVar} {fuel lessFuel : Nat} (lessEv : lessFuel ≤ fuel) :
    REPLSemantics repl fuel → REPLSemantics repl lessFuel := by
  intro replSemantics name type binding
  exact Semantics.monotone lessEv (replSemantics name type binding)

lemma REPLSemantics.extend {TermVar : Type} [DecidableEq TermVar]
    {repl : REPL TermVar} {fuel : Nat} {name : TermVar} {value : input.Denotation}
    (oldReplSemantics : REPLSemantics repl fuel) (extra : Semantics input value fuel) :
    REPLSemantics (repl.extend name value) fuel := by
  intro testedName type binding
  by_cases sameName : testedName = name
  · subst sameName
    simp at binding ⊢
    cases binding
    simpa using extra
  · have tailBinding : repl.env.get testedName = some type := by
      simpa [REPL.extend, sameName] using binding
    simpa [REPL.extend, sameName] using
      oldReplSemantics testedName type tailBinding

theorem fundamental {TermVar : Type} [DecidableEq TermVar] [Inhabited TermVar]
    (repl : REPL TermVar) (newTerm : Env.ScopedTerm repl.env type) :
    ∀ {fuel : Nat},
      REPLSemantics repl fuel →
      Semantics type (repl.eval newTerm) fuel := by
  let rec go {type : Ty} {term : Tm} (repl : REPL TermVar)
      (checked : Env.Checked repl.env term type) :
      ∀ {fuel : Nat},
        REPLSemantics repl fuel →
        Semantics type (repl.eval ⟨term, checked⟩) fuel := by
    match checked with
    | .var binding =>
        intro fuel replSemantics
        simpa [REPL.eval] using replSemantics _ _ binding
    | .literal normalForm =>
        intro fuel replSemantics
        simp [Semantics]
    | @Env.Checked.function _ _ _ body input output bodyChecked =>
        intro fuel replSemantics
        change
          ∀ lessFuel, lessFuel ≤ fuel →
            ∀ value, Semantics input value lessFuel →
              Later
                (Semantics output
                  ((repl.eval ⟨Tm.function body, Env.Checked.function bodyChecked⟩) value) lessFuel)
        intro lessFuel smallerBound value valueSemantics
        refine ⟨?_⟩
        simpa [REPL.eval] using
          go (repl.extend (input := input) default value) (bodyChecked default)
            (fuel := lessFuel)
            ((REPLSemantics.monotone smallerBound replSemantics).extend valueSemantics)
    | @Env.Checked.apply _ _ _ function argument input output functionChecked argumentChecked =>
        intro fuel replSemantics
        have functionSemantics :
            ∀ lessFuel, lessFuel ≤ fuel →
              ∀ value, Semantics input value lessFuel →
                Later
                  (Semantics output
                    ((repl.eval ⟨function, functionChecked⟩) value) lessFuel) := by
          simpa [Semantics] using
            go repl functionChecked
              (fuel := fuel)
              replSemantics
        have argumentSemantics :
            Semantics input (repl.eval ⟨argument, argumentChecked⟩) fuel :=
          go repl argumentChecked
            (fuel := fuel)
            replSemantics
        simpa [REPL.eval] using
          (functionSemantics fuel le_rfl
            (repl.eval ⟨argument, argumentChecked⟩) argumentSemantics).force
  cases newTerm with
  | mk term checked =>
      intro fuel replSemantics
      simpa using go repl checked (fuel := fuel) replSemantics

abbrev closed (TermVar : Type) [DecidableEq TermVar] (type : Ty) :=
  Env.ScopedTerm (env := (Env.empty : Env TermVar)) type

theorem soundness {TermVar : Type} [DecidableEq TermVar] [Inhabited TermVar]
    (term : closed TermVar type) :
    ∀ fuel, ∃ value,
      (REPL.empty : REPL TermVar).RunsTo term value ∧
      Semantics type value fuel := by
  intro fuel
  refine ⟨(REPL.empty : REPL TermVar).eval term, ?_, ?_⟩
  · rfl
  · exact fundamental (REPL.empty : REPL TermVar) term (fuel := fuel) (by
      intro _name _innerType binding
      simp at binding)

end STLC
