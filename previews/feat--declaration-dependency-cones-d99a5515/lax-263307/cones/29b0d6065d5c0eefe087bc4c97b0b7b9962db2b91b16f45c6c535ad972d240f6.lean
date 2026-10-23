-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Rat.Floor
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

-- Lax263307.ConditionedCosts
section
namespace Lax263307.ConditionedCosts
end Lax263307.ConditionedCosts
end

-- Lax263307.ComponentCuts
section
namespace Lax263307.ComponentCuts
end Lax263307.ComponentCuts
end

-- Lax263307.SeparatorComponents
section
namespace Lax263307.SeparatorComponents

/-- A partition of the undeleted vertices, closed under undeleted edges. -/
structure Partition {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (ι : Type) where
  /-- The original vertices in each part. -/
  vertices : ι → Finset (Fin n)
  /-- Parts exclude the deleted vertices. -/
  outside : ∀ i v, v ∈ vertices i → v ∉ S
  /-- Every undeleted vertex belongs to exactly one part. -/
  unique : ∀ v, v ∉ S → ∃! i, v ∈ vertices i
  /-- No undeleted edge leaves a part. -/
  closed : ∀ i u v, u ∈ vertices i → v ∉ S → G.Adj u v → v ∈ vertices i

/-- The recursive answer is the union of the answers on the parts. -/
def combine {n : ℕ} {ι : Type} [Fintype ι] (I : ι → Finset (Fin n)) :
    Finset (Fin n) := Finset.univ.biUnion I

end Lax263307.SeparatorComponents
end

-- Lax263307.RecursiveRounding
section
namespace Lax263307.RecursiveRounding
end Lax263307.RecursiveRounding
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
end Lax263307.StrongComponentGaps
end

-- Lax263307.HeavyRecursiveRounding
section
namespace Lax263307.HeavyRecursiveRounding
end Lax263307.HeavyRecursiveRounding
end

-- Lax263307.ComputedRounding
section
namespace Lax263307.ComputedRounding

open SeparatorComponents (combine)

def target (δ cost : ℚ) : ℕ := ⌊(1 - δ) * cost⌋₊ + 1

def answer {n : ℕ} {ι : Type} (δ : ℚ) (k : ℕ) (cost : ι → ℚ)
    (query : ι → ℕ → Option (Finset (Fin n))) (i : ι) : Option (Finset (Fin n)) :=
  if δ * k / (4 * n) < cost i then query i (target δ (cost i)) else some ∅

inductive Result (n : ℕ)
  | found (vertices : Finset (Fin n))
  | cut (vertices : Finset (Fin n)) (bound : ℕ)

def collect {n : ℕ} {ι : Type} [Fintype ι] (order : List ι) (parts : ι → Finset (Fin n))
    (δ : ℚ) (k : ℕ) (cost : ι → ℚ) (query : ι → ℕ → Option (Finset (Fin n))) : Result n :=
  match order.find? (fun i => (answer δ k cost query i).isNone) with
  | some i => .cut (parts i) (target δ (cost i) - 1)
  | none => .found (combine (fun i => (answer δ k cost query i).getD ∅))

open LinearRelaxation SeparatorComponents

open ComponentCutEncoding

axiom collect_correct {n r : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (k h : ℕ) (δ : ℚ) (η : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hδ : 0 < δ) (small : δ ≤ 1 / 4) (hη : 0 < η)
    (x y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A S : Finset (Fin n)) (P : Partition G S ι) (size : A.card ≤ r)
    (moment : η ≤ value y A) (count : Fintype.card ι ≤ 2 * n)
    (light : ∑ v ∈ S, conditioned y A v ≤ (δ : ℝ) * k)
    (order : List ι) (complete : ∀ i, i ∈ order)
    (c : ι → ℚ) (cost_cast : ∀ i, (c i : ℝ) = ∑ v ∈ P.vertices i, conditioned y A v)
    (query : ι → ℕ → Option (Finset (Fin n)))
    (queries : ∀ i, δ * k / (4 * n) < c i →
      match query i (target δ (c i)) with
      | some I => I ⊆ P.vertices i ∧ G.IsIndepSet (I : Set (Fin n)) ∧
          (1 - 4 * (δ : ℝ)) ^ h * (target δ (c i) : ℝ) ≤ I.card
      | none => IsIndependenceBound G (P.vertices i) (target δ (c i) - 1))
    (near : ∀ B, |x B - y B| ≤ η * (δ : ℝ) ^ 2 / (32 * (n : ℝ) ^ 2)) :
    match collect order P.vertices δ k c query with
    | .found I => G.IsIndepSet (I : Set (Fin n)) ∧
        (1 - 4 * (δ : ℝ)) ^ (h + 1) * (k : ℝ) ≤ I.card
    | .cut C u => u ≤ n ∧ IsIndependenceBound G C u ∧
        (∀ z ∈ independentSetHull G k r, evaluate (coefficient A C u) z ≤ 0) ∧
        η * (δ : ℝ) ^ 2 / (16 * n) ≤ evaluate (coefficient A C u) x ∧
        (∑ B : Coordinate n r, |(coefficient A C u B : ℝ)|) ≤ 2 * n

end Lax263307.ComputedRounding
end
