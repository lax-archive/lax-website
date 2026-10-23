-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Powerset
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

/-- Vertex costs after conditioning on inclusion of `A`. -/
noncomputable def conditioned {n r : ℕ} (y : MomentVector n r)
    (A : Finset (Fin n)) (v : Fin n) : ℝ :=
  value y (insert v A) / value y A

/-- A certified upper bound on independent sets contained in a vertex set. -/
def IsIndependenceBound {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (u : ℕ) : Prop :=
  ∀ J : Finset (Fin n), J ⊆ C → G.IsIndepSet (J : Set (Fin n)) → J.card ≤ u

end Lax263307.LinearRelaxation
end

-- Lax263307.ComponentCuts
section
namespace Lax263307.ComponentCuts
end Lax263307.ComponentCuts
end

-- Lax263307.ComponentCutEncoding
section
namespace Lax263307.ComponentCutEncoding

open LinearRelaxation

/-- The coefficient at one coordinate, after collecting all repeated terms. -/
def coefficient {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (B : Coordinate n r) : ℤ :=
  (∑ v ∈ C, if insert v A = B.val then 1 else 0) -
    if A = B.val then (u : ℤ) else 0

/-- Evaluate the coefficient vector in the real coordinate space. -/
noncomputable def evaluate {n r : ℕ} (a : Coordinate n r → ℤ)
    (z : MomentVector n r) : ℝ := ∑ B, (a B : ℝ) * z B

end Lax263307.ComponentCutEncoding
end

-- Lax263307.StrongComponentGaps
section
namespace Lax263307.StrongComponentGaps

open LinearRelaxation ComponentCutEncoding

axiom component_gap {n r : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (y : MomentVector n r) (A C : Finset (Fin n)) (u : ℕ)
    (size : A.card ≤ r) (bound : IsIndependenceBound G C u)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n) (hk : 0 < k)
    (moment : η ≤ value y A)
    (heavy : δ * (k : ℝ) / (2 * n) ≤ ∑ v ∈ C, conditioned y A v)
    (rounded : (u : ℝ) ≤ (1 - δ) * ∑ v ∈ C, conditioned y A v) :
    (∀ z ∈ independentSetHull G k r, evaluate (coefficient A C u) z ≤ 0) ∧
      η * δ ^ 2 * (k : ℝ) / (2 * n) ≤ evaluate (coefficient A C u) y

end Lax263307.StrongComponentGaps
end
