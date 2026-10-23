-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

-- Lax263307.LinearRelaxation
section
namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible

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

/-- The convex hull of encodings of size-`k` independent sets. -/
def independentSetHull {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    Set (MomentVector n r) :=
  convexHull ℝ {y | ∃ I : Finset (Fin n),
    G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k ∧ y = indicator r I}

/-- A certified upper bound on independent sets contained in a vertex set. -/
def IsIndependenceBound {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (u : ℕ) : Prop :=
  ∀ J : Finset (Fin n), J ⊆ C → G.IsIndepSet (J : Set (Fin n)) → J.card ≤ u

end Lax263307.LinearRelaxation
end

-- Lax263307.ComponentCuts
section
namespace Lax263307.ComponentCuts

open LinearRelaxation

/-- A certified independence bound supplies an inequality valid on the exact hull. -/
axiom valid_cut {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (C : Finset (Fin n)) (u : ℕ) (bound : IsIndependenceBound G C u)
    (A : Finset (Fin n)) (size : A.card ≤ r)
    (z : MomentVector n r) (member : z ∈ independentSetHull G k r) :
    ∑ v ∈ C, value z (insert v A) ≤ (u : ℝ) * value z A

end Lax263307.ComponentCuts
end
