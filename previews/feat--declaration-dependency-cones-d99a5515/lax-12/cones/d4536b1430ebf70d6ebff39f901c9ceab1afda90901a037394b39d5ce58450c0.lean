-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

-- Lax12.GraphClasses
section
namespace Lax12.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax12.GraphClasses
end

-- Lax12.NeighborhoodComplexity
section
namespace Lax12.NeighborhoodComplexity

open Lax12.GraphClasses

/-- The number of distinct neighborhood traces `N(v) ∩ A` that the
vertices of `G` leave on the vertex set `A`. -/
noncomputable def traceCount {V : Type*} (G : SimpleGraph V)
    (A : Set V) : ℕ :=
  {S : Set V | ∃ v : V, S = G.neighborSet v ∩ A}.ncard

/-- Every graph in the class leaves at most `c · |A|^(1+ε)` neighborhood
traces on every nonempty vertex subset `A`, where `c` depends only on
`ε > 0`: neighborhood complexity `|A|^(1+o(1))`. -/
def HasAlmostLinearNC (C : GraphClass) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Set (Fin n), A.Nonempty →
        (traceCount G A : ℝ) ≤ c * (A.ncard : ℝ) ^ (1 + ε)

end Lax12.NeighborhoodComplexity
end

-- Lax12.NowhereDenseClasses
section
namespace Lax12.NowhereDenseClasses

open Lax12.GraphClasses

/-- A model of `H` as a depth-`r` minor of `G`: pairwise disjoint branch
sets, each spanned by walks of length at most `r` from a center vertex
(hence connected of radius at most `r`), with an edge of `G` between the
branch sets of any two adjacent vertices of `H`. -/
structure ShallowMinorModel {V W : Type*} (r : ℕ) (H : SimpleGraph W)
    (G : SimpleGraph V) where
  /-- The branch set of each vertex of `H`. -/
  branch : W → Set V
  /-- The center of each branch set. -/
  center : W → V
  /-- Centers lie in their branch sets (so branch sets are nonempty). -/
  center_mem : ∀ u, center u ∈ branch u
  /-- Distinct branch sets are disjoint. -/
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  /-- Every vertex of a branch set is reached from the center by a walk
  of length at most `r` inside the branch set. -/
  radius_le : ∀ u, ∀ x ∈ branch u, ∃ w : G.Walk (center u) x,
    w.length ≤ r ∧ ∀ y ∈ w.support, y ∈ branch u
  /-- Adjacent vertices of `H` have adjacent branch sets. -/
  adj : ∀ u v, H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

/-- `H` is a minor of `G` at depth `r`. -/
def HasShallowMinor {V W : Type*} (G : SimpleGraph V) (r : ℕ)
    (H : SimpleGraph W) : Prop :=
  Nonempty (ShallowMinorModel r H G)

/-- A graph class is nowhere dense if for every depth `r` some complete
graph is not a depth-`r` minor of any member. -/
def NowhereDense (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ HasShallowMinor G r (⊤ : SimpleGraph (Fin t))

end Lax12.NowhereDenseClasses
end

-- Lax12.NowhereDenseNC
section
namespace Lax12.NowhereDenseNC

open Lax12.GraphClasses Lax12.NeighborhoodComplexity Lax12.NowhereDenseClasses

/-- Nowhere dense graph classes have almost linear neighborhood
complexity. -/
axiom hasAlmostLinearNC_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    HasAlmostLinearNC C

end Lax12.NowhereDenseNC
end
