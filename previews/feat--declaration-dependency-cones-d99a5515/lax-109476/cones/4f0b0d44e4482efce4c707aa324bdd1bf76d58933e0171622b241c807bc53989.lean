-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

-- Lax109476.LinearProgram
section
open scoped BigOperators

namespace Lax109476.LinearProgram

/-- Coefficients of a maximization program with `m` inequalities and `n`
nonnegative variables. -/
structure Program (K : Type) (m n : ℕ) where
  /-- The constraint matrix. -/
  A : Fin m → Fin n → K
  /-- The upper bounds on the constraint rows. -/
  b : Fin m → K
  /-- The coefficients of the maximized objective. -/
  c : Fin n → K

/-- The value of one constraint row at a primal point. -/
def rowValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) (i : Fin m) : K :=
  ∑ j, P.A i j * x j

/-- The primal objective value. -/
def primalValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) : K :=
  ∑ j, P.c j * x j

/-- A nonnegative primal point satisfies all row upper bounds. -/
def PrimalFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (x : Fin n → K) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, rowValue P x i ≤ P.b i

/-- A finite upper bound holds for every real primal feasible point. -/
def IsBoundedAbove {m n : ℕ} (P : Program ℝ m n) : Prop :=
  ∃ B : ℝ, ∀ x, PrimalFeasible P x → primalValue P x ≤ B

end Lax109476.LinearProgram
end

-- Lax109476.RecessionDirection
section
namespace Lax109476.RecessionDirection

open Lax109476.LinearProgram

/-- A nonnegative direction preserves every upper constraint and improves
the maximized objective. -/
def IsImprovingDirection {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (d : Fin n → K) : Prop :=
  (∀ j, 0 ≤ d j) ∧ (∀ i, rowValue P d i ≤ 0) ∧ 0 < primalValue P d

end Lax109476.RecessionDirection
end

-- Lax109476.RecessionSoundness
section
namespace Lax109476.RecessionSoundness

open Lax109476.LinearProgram Lax109476.RecessionDirection

/-- A feasible base point and an improving direction rule out any objective bound. -/
axiom direction_not_bounded :
  ∀ (m n : ℕ) (P : Program ℝ m n) (x d : Fin n → ℝ),
    PrimalFeasible P x → IsImprovingDirection P d → ¬ IsBoundedAbove P

end Lax109476.RecessionSoundness
end
