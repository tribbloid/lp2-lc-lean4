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

section

variable {TermVar : Type} [DecidableEq TermVar]

/--
Step-indexed logical relation describing semantically well-behaved values.
-/
def Semantics (type : Ty) (ir : type.Denotation) (fuel : Nat) : Prop :=
  match type with
  | .base => True
  | .arrow tIn tOut =>
      let fn := ir
      ∀ lessFuel, lessFuel ≤ fuel →
        ∀ (vIn : tIn.Denotation), Semantics tIn vIn lessFuel →
          Later (Semantics tOut (fn vIn) lessFuel)

/--
proof of monotonicity so the proposition can be moved forward on time axis

all monotonicity proof are pure Slop and should be reduced to 1 line using iris-lean or sledgehammer

but they are unstable right now
-/
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


def REPLSemantics (repl : REPL TermVar) (fuel : Nat) : Prop :=
  ∀ (name : TermVar) (type : Ty) (binding : repl.env.get name = some type),
    Semantics type (repl.varLookup name type binding) fuel

lemma REPLSemantics.monotone {repl : REPL TermVar} {fuel lessFuel : Nat} (lessEv : lessFuel ≤ fuel) :
    REPLSemantics repl fuel → REPLSemantics repl lessFuel := by
  intro replSemantics name type binding
  exact Semantics.monotone lessEv (replSemantics name type binding)

lemma REPLSemantics.extend {repl : REPL TermVar} {fuel : Nat} {name : TermVar} {value : tIn.Denotation}
    (oldReplSemantics : REPLSemantics repl fuel) (extra : Semantics tIn value fuel) :
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

section

variable [Inhabited TermVar]

theorem fundamental (repl : REPL TermVar) (newTerm : Env.ScopedTerm repl.env type) :
    ∀ {fuel : Nat},
      REPLSemantics repl fuel →
      Semantics type (repl.eval newTerm) fuel := by
  let rec go {type : Ty} {tOut : Tm} (repl : REPL TermVar)
      (checked : Env.Checked repl.env tOut type) :
      ∀ {fuel : Nat},
        REPLSemantics repl fuel →
        Semantics type (repl.eval ⟨tOut, checked⟩) fuel := by
    match checked with
    | .var binding =>
        intro fuel replSemantics
        simpa [REPL.eval] using replSemantics _ _ binding
    | .literal normalForm =>
        intro fuel replSemantics
        simp [Semantics]
    | @Env.Checked.function _ _ _ body tIn tOut bodyChecked =>
        intro fuel replSemantics
        change
          ∀ lessFuel, lessFuel ≤ fuel →
            ∀ value, Semantics tIn value lessFuel →
              Later
                (Semantics tOut
                  ((repl.eval ⟨Tm.function body, Env.Checked.function bodyChecked⟩) value) lessFuel)
        intro lessFuel smallerBound value valueSemantics
        refine ⟨?_⟩
        simpa [REPL.eval] using
          go (repl.extend (input := tIn) default value) (bodyChecked default)
            (fuel := lessFuel)
            ((REPLSemantics.monotone smallerBound replSemantics).extend valueSemantics)
    | @Env.Checked.apply _ _ _ function argument tIn tOut functionChecked argumentChecked =>
        intro fuel replSemantics
        have functionSemantics :
            ∀ lessFuel, lessFuel ≤ fuel →
              ∀ value, Semantics tIn value lessFuel →
                Later
                  (Semantics tOut
                    ((repl.eval ⟨function, functionChecked⟩) value) lessFuel) := by
          simpa [Semantics] using
            go repl functionChecked
              (fuel := fuel)
              replSemantics
        have argumentSemantics :
            Semantics tIn (repl.eval ⟨argument, argumentChecked⟩) fuel :=
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

abbrev closed (type : Ty) :=
  Env.ScopedTerm (env := (Env.empty : Env TermVar)) type

theorem soundness (term : closed type) :
    ∀ fuel, ∃ value,
      (REPL.empty : REPL TermVar).canEvalTo term value ∧
      Semantics type value fuel := by
  intro fuel
  refine ⟨(REPL.empty : REPL TermVar).eval term, ?_, ?_⟩
  · rfl
  · exact fundamental (REPL.empty : REPL TermVar) term (fuel := fuel) (by
      intro _name _innerType binding
      simp at binding)

end

end

end STLC
