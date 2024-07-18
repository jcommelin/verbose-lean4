import Verbose.Dutch.Fix

open Lean Elab Tactic

syntax "Neem aan dat₁ " colGt assumeDecl : tactic
syntax "Neem aan dat " (colGt assumeDecl)+ : tactic
-- syntax "Neem " (colGt assumeDecl)+ "aan" : tactic
syntax "Uit het ongerijmde. " "Neem aan dat " (colGt assumeDecl) : tactic

elab_rules : tactic
  | `(tactic| Neem aan dat₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Neem aan dat₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Neem aan dat₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Neem aan dat₁ $decl:assumeDecl))

macro_rules
  | `(tactic| Neem aan dat $decl:assumeDecl) => `(tactic| Supposons₁ $decl)
  | `(tactic| Neem aan dat $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Neem aan dat₁ $decl; Neem aan dat $decls:assumeDecl*)

elab_rules : tactic
  | `(tactic| Uit het ongerijmede. Neem aan dat $x:ident : $type) => forContradiction x.getId type

setLang fr

example (P Q : Prop) : P → Q → True := by
  Neem aan dat hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Neem aan dat hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Neem aan dat hn
  trivial

example : ∀ n > 0, true := by
  success_if_fail_with_msg "Er is hier geen aanname die aangenomen kan worden."
    Neem aan dat n
  intro n
  Neem aan dat H : n > 0
  trivial


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Neem aan dat hP
  Uit het ongerijmede. Neem aan dat hnQ :¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Neem aan dat hP
  Uit het ongerijmde. Neem aan dat hnQ : ¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : Q → ¬ P) : P → ¬ Q := by
  Supposons hP
  Supposons hnQ : Q
  exact h hnQ hP

example : ∀ n > 0, n = n := by
  Supposons par l'absurde H : ∃ n > 0, n ≠ n
  tauto

example : 0 ≠ 1 := by
  success_if_fail_with_msg
    "Le but est déjà une négation, le démontrer par l’absurde n’apporte rien. Vous pouvez directement supposer 0 = 1."
    Supposons par l'absurde h : 0 = 1
  norm_num

example : 0 ≠ 1 := by
  Supposons h : 0 = 1
  norm_num at h

allowProvingNegationsByContradiction

example : 0 ≠ 1 := by
  Supposons par l'absurde h : 0 = 1
  norm_num at h
