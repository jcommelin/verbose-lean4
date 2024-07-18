import Verbose.Tactics.Statements
import Verbose.Dutch.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := fr) mkWidgetProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic) :=
Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions $prf)

/- **TODO**  Allow omitting Gegeven or Aannames. -/

elab name?:(ident)? ("Opgave"<|>"Voorbeeld") str
    "Gegeven :" objs:bracketedBinder*
    "Aannames :" hyps:bracketedBinder*
    "Conclusie :" concl:term
    tkp:"Bewijs :" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise name? objs hyps concl prf? tkp tkq
