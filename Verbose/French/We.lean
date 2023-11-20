import Verbose.Tactics.We
import Verbose.French.Common

open Lean Elab Parser Tactic

declare_syntax_cat becomes
syntax colGt " qui devient " term : becomes

def extractBecomes (e : Lean.TSyntax `becomes) : Lean.Term := ⟨e.raw[1]!⟩

elab rw:"On" " réécrit via " s:myRwRuleSeq l:(location)? new:(becomes)? : tactic => do
  rewriteTac rw s (l.map expandLocation) (new.map extractBecomes)

elab rw:"On" " réécrit via " s:myRwRuleSeq " partout" : tactic => do
  rewriteTac rw s (some Location.wildcard) none

elab "On" " discute en utilisant " exp:term : tactic =>
  discussOr exp

elab "On" " discute selon que " exp:term : tactic =>
  discussEm exp

elab "On" " conclut par " e:maybeApplied : tactic => do
  concludeTac (← maybeAppliedToTerm e)

elab "On" " combine [" prfs:term,* "]" : tactic => do
  combineTac prfs.getElems

elab "On" " calcule " loc:(location)? : tactic => do
  computeTac loc

elab "On" " applique " exp:term : tactic => do
  evalApply (← `(tactic|apply $exp))

macro "On" " forget" args:(ppSpace colGt term:max)+ : tactic => `(tactic|clear $args*)

macro "On" " reformulate " h:ident " as " new:term : tactic => `(tactic|change $new at $h:ident)

example (P Q : Prop) (h : P ∨ Q) : True := by
  On discute en utilisant h
  . intro _hP
    trivial
  . intro _hQ
    trivial


example (P : Prop) : True := by
  On discute selon que P
  . intro _hP
    trivial
  . intro _hnP
    trivial

set_option linter.unusedVariables false in
example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P := by
  success_if_fail_with_msg "application type mismatch
  hRP hQ
argument
  hQ
has type
  Q : Prop
but is expected to have type
  R : Prop"
    On conclut par hRP appliqué à hQ
  On conclut par hRP appliqué à hR

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  On conclut par h appliqué à _

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  On conclut par h

example {a b : ℕ}: a + b = b + a := by
  On calcule

example {a b : ℕ} (h : a + b - a = 0) : b = 0 := by
  On calcule at h
  On conclut par h

variable (k : Nat)

example (h : True) : True := by
  On conclut par h

example (h : ∀ _n : ℕ, True) : True := by
  On conclut par h appliqué à 0

example (h : True → True) : True := by
  On applique h
  trivial

example (h : ∀ _n _k : ℕ, True) : True := by
  On conclut par h appliqué à [0, 1]

example (a b : ℕ) (h : a < b) : a ≤ b := by
  On conclut par h

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b := by
  On conclut par h

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  On combine [h, h']

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 := by
  On combine [h, h']

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c := by
  On combine [h, h']

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  On réécrit via ← h
  On conclut par h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  On réécrit via h at h'
  On conclut par h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  On réécrit via ← h at h' qui devient a = 0
  exact h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  On réécrit via ← h at h'
  clear h
  exact h'

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 := by
  On réécrit via h
  exact hn

example (f : ℕ → ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 := by
  On réécrit via h
  norm_num

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  success_if_fail_with_msg "Given term
  a = c
is not definitionally equal to the expected
  b = c
"
    On réécrit via [h] at h' qui devient a = c
  On réécrit via [h] at h' qui devient b = c
  On conclut par h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c := by
  On réécrit via h partout
  On conclut par h'

/-
example (P Q R : Prop) (h : P → Q) (h' : P) : Q := by
  On applique h to h'
  On conclut par h' -/

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  On conclut par h appliqué à [hP, hQ]

/- example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
  On applique f to h
  On conclut par h

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  On applique h to 0
  On conclut par h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  On contrapose
  intro h
  use x/2
  split
   On conclut par h, -- linarith
  On conclut par h, -- linarith
 -/
example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by On conclut par h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by On conclut par h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by On conclut par h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by On conclut par h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by On conclut par h

/- example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  On contrapose simply
  intro h
  On push the negation
  On push the negation at h
  use x/2
  split
   On conclut par h, -- linarith
  On conclut par h, -- linarith

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  On contrapose simply
  intro h
  success_if_fail_with_msg ""
    On push the negation qui devient 0 < x
  On push the negation
  success_if_fail_with_msg ""
    On push the negation at h qui devient ∃ (ε : ℝ), ε > 0 ∧ ε < x
  On push the negation at h qui devient 0 < x
  use x/2
  split
   On conclut par h, -- linarith
  On conclut par h, -- linarith

example : (∀ n : ℕ, false) → 0 = 1 := by
  On contrapose
  On calcule
 -/
example (P Q : Prop) (h : P ∨ Q) : True := by
  On discute en utilisant h
  all_goals
    intro
    trivial

example (P : Prop) (hP₁ : P → True) (hP₂ : ¬ P → True): True := by
  On discute selon que P
  intro h
  exact hP₁ h
  intro h
  exact hP₂ h

def f (n : ℕ) := 2*n
/-
example : f 2 = 4 := by
  On unfold f
  refl

example (h : f 2 = 4) : True → True := by
  On unfold f at h
  guard_hyp_strict h : 2*2 = 4
  exact id

example (h : f 2 = 4) : True → True := by
  success_if_fail_with_msg ""
    On unfold f at h qui devient 2*2 = 5
  On unfold f at h qui devient 2*2 = 4
  exact id

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  On rename n to p at h
  On rename k to l at h
  guard_hyp_strict h : ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  On rename n to p at h qui devient ∀ p, ∃ k, P p k
  success_if_fail_with_msg ""
    On rename k to l at h qui devient ∀ p, ∃ j, P p j
  On rename k to l at h qui devient ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ True := by
  On rename n to p
  On rename k to l
  guard_target_strict (∀ p, ∃ l, P p l) ∨ True
  right
  trivial
 -/
example (a b c : ℕ) : True := by
  On forget a
  On forget b c
  trivial

example (h : 1 + 1 = 2) : True := by
  success_if_fail_with_msg "type mismatch
  this
has type
  2 = 3 : Prop
but is expected to have type
  1 + 1 = 2 : Prop"
    On reformulate h as 2 = 3
  On reformulate h as 2 = 2
  trivial
