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

/-- The real primal feasible set is nonempty. -/
def IsFeasible {m n : ℕ} (P : Program ℝ m n) : Prop :=
  ∃ x, PrimalFeasible P x

/-- A finite upper bound holds for every real primal feasible point. -/
def IsBoundedAbove {m n : ℕ} (P : Program ℝ m n) : Prop :=
  ∃ B : ℝ, ∀ x, PrimalFeasible P x → primalValue P x ≤ B

/-- A primal feasible point maximizes the objective over the feasible set. -/
def IsPrimalOptimal {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (x : Fin n → K) : Prop :=
  PrimalFeasible P x ∧ ∀ z, PrimalFeasible P z → primalValue P z ≤ primalValue P x

end Lax109476.LinearProgram
end

-- Lax109476.PrimalAttainment
section
namespace Lax109476.PrimalAttainment

open Lax109476.LinearProgram

/-- A nonempty polyhedron attains every bounded-above linear objective. -/
axiom exists_primal_optimizer :
  ∀ (m n : ℕ) (P : Program ℝ m n), IsFeasible P → IsBoundedAbove P →
    ∃ x : Fin n → ℝ, IsPrimalOptimal P x

end Lax109476.PrimalAttainment
end
