import Verbose.Tactics.Set
import Mathlib.Tactic

elab "Zij " n:maybeTypedIdent " := " val:term : tactic => do
  let (n, ty) := match n with
  | `(maybeTypedIdent| $N:ident) => (N, none)
  | `(maybeTypedIdent|($N : $TY)) => (N, some TY)
  | _ => (default, none)
  setTac n ty val


example (a b : ℕ) : ℕ := by
  Zij n := max a b
  exact n

example (a b : ℕ) : ℕ := by
  Zij (n : ℕ) := max a b
  exact n

example : ℤ := by
  Zij (n : ℤ) := max 0 1
  exact n
