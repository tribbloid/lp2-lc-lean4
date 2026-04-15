import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC.Tests

open Lp2lc.Active.STLC

local notation "BoolT" => Ty.bool

def fals : TermClosed BoolT :=
  .fals

def tru : TermClosed BoolT :=
  .tru

def ident : TermClosed (BoolT ==> BoolT) :=
  .abs (fun x => .var x)

def falsAgain : TermClosed BoolT :=
  .app ident fals

def first : TermClosed (BoolT ==> BoolT ==> BoolT) :=
  .abs (fun x => .abs (fun _y => .var x))

def second : TermClosed (BoolT ==> BoolT ==> BoolT) :=
  .abs (fun _x => .abs (fun y => .var y))

def testFirst : TermClosed BoolT :=
  .app (.app first fals) tru

def testSecond : TermClosed BoolT :=
  .app (.app second fals) tru

def app : TermClosed ((BoolT ==> BoolT) ==> BoolT ==> BoolT) :=
  .abs (fun f => .abs (fun x => .app (.var f) (.var x)))

def falsAgain2 : TermClosed BoolT :=
  .app (.app app ident) fals

end Tests
