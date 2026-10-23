-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

-- Lax199508.GraphClasses
section
namespace Lax199508
end Lax199508

namespace Lax199508.GraphClasses
end Lax199508.GraphClasses
end

-- Lax199508.NowhereDenseClasses
section
namespace Lax199508.NowhereDenseClasses

open Lax199508.GraphClasses

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

end Lax199508.NowhereDenseClasses
end
