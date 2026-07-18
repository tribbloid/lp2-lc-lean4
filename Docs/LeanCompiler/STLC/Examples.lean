import «LeanCompiler».STLC.Compile

namespace LeanCompiler.STLC.Examples

open LeanCompiler.STLC.Source
open LeanCompiler.STLC.CPS
open LeanCompiler.STLC.CPSify
open LeanCompiler.STLC.Compile
open LeanCompiler.STLC.CC

local notation "BoolT" => Ty.bool

def fals : TermClosed BoolT :=
  λ _ => .fals

def tru : TermClosed BoolT :=
  λ _ => .tru

def ident : TermClosed (BoolT ==> BoolT) :=
  λ _ => .abs (λ x => .var x)

def falsAgain : TermClosed BoolT :=
  λ _ => .app (ident _) (fals _)

def first : TermClosed (BoolT ==> BoolT ==> BoolT) :=
  λ _ => .abs (λ x => .abs (λ _y => .var x))

def second : TermClosed (BoolT ==> BoolT ==> BoolT) :=
  λ _ => .abs (λ _x => .abs (λ y => .var y))

def testFirst : TermClosed BoolT :=
  λ _ => .app (.app (first _) (fals _)) (tru _)

def testSecond : TermClosed BoolT :=
  λ _ => .app (.app (second _) (fals _)) (tru _)

def app : TermClosed ((BoolT ==> BoolT) ==> BoolT ==> BoolT) :=
  λ _ => .abs (λ f => .abs (λ x => .app (.var f) (.var x)))

def falsAgain2 : TermClosed BoolT :=
  λ _ => .app (.app (app _) (ident _)) (fals _)

-- Source denotation checks.
example : TermClosed.denote fals = false := rfl
example : TermClosed.denote tru = true := rfl
example : TermClosed.denote falsAgain = false := by
  simp [falsAgain, ident, fals, TermClosed.denote]
example : TermClosed.denote testFirst = false := by
  simp [testFirst, first, fals, tru, TermClosed.denote]
example : TermClosed.denote testSecond = true := by
  simp [testSecond, second, fals, tru, TermClosed.denote]
example : TermClosed.denote falsAgain2 = false := by
  simp [falsAgain2, app, ident, fals, TermClosed.denote]

-- CPS and compile artifacts.
def cpsFals := CpsTerm fals
def cpsTru := CpsTerm tru
def cpsIdent := CpsTerm ident
def cpsFalsAgain := CpsTerm falsAgain
def cpsFirst := CpsTerm first
def cpsSecond := CpsTerm second
def cpsTestFirst := CpsTerm testFirst
def cpsTestSecond := CpsTerm testSecond
def cpsApp := CpsTerm app
def cpsFalsAgain2 := CpsTerm falsAgain2

section Parametric

variable [TermParametricity] [PTermParametricity]

def ccFals := compile fals
def ccTru := compile tru
def ccIdent := compile ident
def ccFalsAgain := compile falsAgain
def ccFirst := compile first
def ccSecond := compile second
def ccTestFirst := compile testFirst
def ccTestSecond := compile testSecond
def ccApp := compile app
def ccFalsAgain2 := compile falsAgain2

example : CProgClosed.denote ccFals (λ b => b) = false := by
  simpa [ccFals, fals] using compile_correct fals

example : CProgClosed.denote ccTestSecond (λ b => b) = true := by
  simpa [ccTestSecond, testSecond, second, fals, tru, TermClosed.denote] using compile_correct testSecond

end Parametric

end LeanCompiler.STLC.Examples
