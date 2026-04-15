import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC.Tests

open Lp2lc.Active.STLC

local notation "BoolT" => Ty.bool

def fals : TermClosed BoolT :=
  fun _ => .fals

def tru : TermClosed BoolT :=
  fun _ => .tru

def ident : TermClosed (BoolT ==> BoolT) :=
  fun _ => .abs (fun x => .var x)

def falsAgain : TermClosed BoolT :=
  fun _ => .app (ident _) (fals _)

def first : TermClosed (BoolT ==> BoolT ==> BoolT) :=
  fun _ => .abs (fun x => .abs (fun _y => .var x))

def second : TermClosed (BoolT ==> BoolT ==> BoolT) :=
  fun _ => .abs (fun _x => .abs (fun y => .var y))

def testFirst : TermClosed BoolT :=
  fun _ => .app (.app (first _) (fals _)) (tru _)

def testSecond : TermClosed BoolT :=
  fun _ => .app (.app (second _) (fals _)) (tru _)

def app : TermClosed ((BoolT ==> BoolT) ==> BoolT ==> BoolT) :=
  fun _ => .abs (fun f => .abs (fun x => .app (.var f) (.var x)))

def falsAgain2 : TermClosed BoolT :=
  fun _ => .app (.app (app _) (ident _)) (fals _)

end Tests
