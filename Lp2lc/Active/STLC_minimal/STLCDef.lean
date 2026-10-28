import «Lp2lc».Active.Util
import «Lp2lc».Active.Parameters

namespace Lp2lc.Active.STLC_minimal

open Lp2lc.Active.Util

namespace Pre

mutual

inductive Binder : Parameters → Label → UAST where

| private body {P} (body : P.Next.TRef → AST P.Next l) : Binder P l

inductive AST : Parameters → Label → UAST where

| TLit {P} : AST P .typ

| lit {P} (repr : P.B) : AST P .val

| TFn {P} (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ

| fn {P} (tIn : AST P .typ) (body : Binder P .trm) : AST P .val

| fnPrimitive {P} (tOut : AST P .typ) (op : P.B → AST P .val) : AST P .val

| ref {P} {P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST P .trm

| val {P} (v : AST P .val) : AST P .trm

| apply {P} (fn : AST P .trm) (arg : AST P .trm) : AST P .trm

end

namespace Binder

def mk := @body

def apply {P l} (self : Binder P l) (carrier) := match self with
  | .body code => code carrier

end Binder

end Pre

end Lp2lc.Active.STLC_minimal
