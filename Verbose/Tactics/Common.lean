import Lean

import Std.Tactic.RCases
import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Tactic

open Lean
open Lean.Parser.Tactic
open Lean Meta
open Lean Elab Tactic
open Option

/-- Check whether a name is available. -/
def checkName (n : Name) : TacticM Unit := do
if (← getLCtx).usesUserName n then
  throwError "The name {n} is already used"
else pure ()

def mkBinderIdent (n : Name) : CoreM (TSyntax ``binderIdent) :=
  `(binderIdent| $(mkIdent n):ident)

def elabTermEnsuringValue (t : Term) (val : Expr) : TermElabM Expr :=
  Term.withSynthesize do
  Term.withoutErrToSorry do
  let e ← Term.elabTerm t none
  -- The `withAssignableSyntheticOpaque` is to be able to assign ?_ metavariables
  unless ← withAssignableSyntheticOpaque <| isDefEq e val do
    throwError "Given term{indentD e}\nis not definitionally equal to the expected{
      ""}{indentD val}"
  return e

def MaybeTypedIdent := Name × Option Term

instance : ToString MaybeTypedIdent where
  toString
  | (n, some t) => s!"({n} : {Syntax.prettyPrint t})"
  | (n, none) => s!"{n}"


open Std Tactic RCases

-- TODO: replace Syntax.missing by something smarter
def RCasesPattOfMaybeTypedIdent : MaybeTypedIdent → RCasesPatt
| (n, some pe) => RCasesPatt.typed Syntax.missing (RCasesPatt.one Syntax.missing  n) pe
| (n, none)    => RCasesPatt.one Syntax.missing n

declare_syntax_cat maybeTypedIdent
syntax ident : maybeTypedIdent
syntax "("ident " : " term")" : maybeTypedIdent
syntax ident " : " term : maybeTypedIdent

-- We could also use the less specific type `Syntax → MaybeTypedIdent`
def toMaybeTypedIdent : TSyntax `maybeTypedIdent → MaybeTypedIdent
| `(maybeTypedIdent| ($x:ident : $type:term)) => (x.getId, type)
| `(maybeTypedIdent| $x:ident : $type:term) => (x.getId, type)
| `(maybeTypedIdent| $x:ident) => (x.getId, none)
| _ => (Name.anonymous, none) -- This should never happen
