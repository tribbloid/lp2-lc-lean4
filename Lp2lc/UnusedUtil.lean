import Lean.Meta.AppBuilder
import «Lp2lc».Util.Rfl

namespace Lp2lc.Util

structure SourcePosition where
  line : Nat
  column : Nat
  deriving Repr, DecidableEq

structure FunctionSource where
  declName : Option Lean.Name := none
  text : Option String := none
  start : Option SourcePosition := none
  stop : Option SourcePosition := none
  deriving Repr, DecidableEq

structure FunctionWrapper (α : Type u) (β : Type v) where
  executable : α → β
  source : FunctionSource := {}

namespace FunctionWrapper

def fromFunction (f : α → β) : FunctionWrapper α β :=
  { executable := f }

instance : Coe (α → β) (FunctionWrapper α β) where
  coe := fromFunction

instance : CoeFun (FunctionWrapper α β) (λ _ => α → β) where
  coe self := self.executable

instance : Repr (FunctionWrapper α β) where
  reprPrec self prec :=
    Repr.addAppParen ("FunctionWrapper " ++ reprArg self.source) prec

end FunctionWrapper

open Lean Elab Term Meta

private def expectedFunctionType? : Option Expr → TermElabM (Option Expr)
  | none => pure none
  | some expectedType => do
      let expectedType ← whnf expectedType
      if expectedType.isAppOfArity ``FunctionWrapper 2 then
        let args := expectedType.getAppArgs
        some <$> mkArrow args[0]! args[1]!
      else
        pure none

private def quoteSourcePosition? : Option Position → TermElabM Term
  | some pos => do
      let line := quote pos.line
      let column := quote pos.column
      `(some ({ line := $line, column := $column } : SourcePosition))
  | none => `(none)

private def quoteName? : Option Name → TermElabM Term
  | some name => `(some $(quote name))
  | none => `(none)

private def quoteString? : Option String → TermElabM Term
  | some text => `(some $(quote text))
  | none => `(none)

private def currentFileRangeText? (fileMap : FileMap) (range : DeclarationRange) :
    Option String :=
  let start := fileMap.ofPosition range.pos
  let stop := fileMap.ofPosition range.endPos
  if start <= stop then
    some (String.Pos.Raw.extract fileMap.source start stop)
  else
    none

private def sourceExpr (declName : Option Name) (text : Option String)
    (start stop : Option Position) : TermElabM Expr := do
  let declNameStx ← quoteName? declName
  let textStx ← quoteString? text
  let startStx ← quoteSourcePosition? start
  let stopStx ← quoteSourcePosition? stop
  let sourceStx ←
    `({ declName := $declNameStx, text := $textStx, start := $startStx, stop := $stopStx })
  elabTerm sourceStx (some (mkConst ``FunctionSource))

private def sourceFromSyntax (fileMap : FileMap) (term : Term) : TermElabM Expr :=
  sourceExpr none
    (term.raw.getSubstring? (withLeading := false) (withTrailing := false) |>.map toString)
    (term.raw.getPos?.map fileMap.toPosition)
    (term.raw.getTailPos?.map fileMap.toPosition)

private def sourceFromDecl? (fileMap : FileMap) (declName : Name) : TermElabM (Option Expr) := do
  let some ranges ← findDeclarationRanges? declName | return none
  let module? ← findModuleOf? declName
  let text := if module?.isNone then currentFileRangeText? fileMap ranges.range else none
  some <$> sourceExpr (some declName) text (some ranges.range.pos) (some ranges.range.endPos)

syntax (name := sourceFunction) "source_function% " term : term

@[term_elab sourceFunction] def elabSourceFunction : TermElab := λ stx expectedType? => do
  let term : Term := ⟨stx[1]⟩
  let executable ← elabTerm term (← expectedFunctionType? expectedType?)
  synthesizeSyntheticMVarsNoPostponing
  let executable ← instantiateMVars executable
  let fileMap ← getFileMap
  let source ←
    match executable.constName? with
    | some declName => do
        match ← sourceFromDecl? fileMap declName with
        | some source => pure source
        | none => sourceFromSyntax fileMap term
    | none => sourceFromSyntax fileMap term
  let wrapper ← mkAppM ``FunctionWrapper.mk #[executable, source]
  ensureHasType expectedType? wrapper

private def sourceFunctionExample (x : Nat) := x + 1

example : (((λ x : Nat => x + 1) : FunctionWrapper Nat Nat) 2) = 3 := rfl

example : ((source_function% (λ x => x + 1) : FunctionWrapper Nat Nat) 2) = 3 := rfl

example :
    (source_function% (λ x => x + 1) : FunctionWrapper Nat Nat).source.text.isSome =
      true := rfl

example :
    (source_function% sourceFunctionExample : FunctionWrapper Nat Nat).source.declName.isSome =
      true := rfl

end Lp2lc.Util
