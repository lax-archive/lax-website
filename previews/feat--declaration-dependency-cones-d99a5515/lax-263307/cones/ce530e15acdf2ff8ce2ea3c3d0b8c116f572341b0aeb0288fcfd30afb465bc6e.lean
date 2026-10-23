-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

-- Lax263307.LinearRelaxation
section
namespace Lax263307.LinearRelaxation

/-- The coordinate sets of the level-`r` relaxation. -/
abbrev Coordinate (n r : ℕ) := {A : Finset (Fin n) // A.card ≤ r + 2}

/-- A vector with precisely the coordinates used by the relaxation. -/
abbrev MomentVector (n r : ℕ) := Coordinate n r → ℝ

/-- Read a coordinate, returning zero outside the truncated coordinate domain. -/
def value {n r : ℕ} (y : MomentVector n r) (A : Finset (Fin n)) : ℝ :=
  if h : A.card ≤ r + 2 then y ⟨A, h⟩ else 0

/-- The indicator encoding of a vertex set. -/
def indicator {n : ℕ} (r : ℕ) (I : Finset (Fin n)) : MomentVector n r :=
  fun A => if A.val ⊆ I then 1 else 0

/-- The five families of linear constraints defining `R_r(G,k)`. -/
structure IsFeasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) : Prop where
  /-- The empty moment is normalized. -/
  normalized : value y ∅ = 1
  /-- Each moment lies in the unit interval. -/
  bounds : ∀ A, 0 ≤ y A ∧ y A ≤ 1
  /-- Adding a vertex cannot increase a moment. -/
  monotone : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∀ v, value y (insert v A) ≤ value y A
  /-- Nonindependent sets have zero moment. -/
  vanishes : ∀ A : Coordinate n r, ¬G.IsIndepSet (A.val : Set (Fin n)) → y A = 0
  /-- The cardinality constraint remains valid after conditioning. -/
  mass : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∑ v : Fin n, value y (insert v A) = (k : ℝ) * value y A

/-- The convex hull of encodings of size-`k` independent sets. -/
def independentSetHull {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    Set (MomentVector n r) :=
  convexHull ℝ {y | ∃ I : Finset (Fin n),
    G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k ∧ y = indicator r I}

end Lax263307.LinearRelaxation
end

-- Lax263307.RelaxationFeasibility
section
namespace Lax263307.RelaxationFeasibility

open LinearRelaxation

/-- The exact independent-set hull is contained in the relaxation. -/
axiom hull_feasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (member : y ∈ independentSetHull G k r) :
    IsFeasible G k r y

end Lax263307.RelaxationFeasibility
end
