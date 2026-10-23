-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax199508.GraphClasses
section
namespace Lax199508.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax199508.GraphClasses
end

-- Lax195003.WelzlOrdersNeighborhoodComplexity
section
namespace Lax195003.WelzlOrdersNeighborhoodComplexity

open Lax199508.GraphClasses

/-- The number of distinct traces `N(v) ∩ A` that vertex neighborhoods leave
on the vertex set `A`. -/
noncomputable def traceCount {V : Type*} (G : SimpleGraph V)
    (A : Set V) : ℕ :=
  {S : Set V | ∃ v : V, S = G.neighborSet v ∩ A}.ncard

/-- The maximum number of distinct neighborhood traces on a vertex set of
cardinality at most `k`. -/
noncomputable def neighborhoodComplexity {n : ℕ}
    (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  sSup {q : ℕ | ∃ A : Set (Fin n),
    A.ncard ≤ k ∧ q = traceCount G A}

/-- The graph `G` has neighborhood complexity at most `c · k` for every
positive `k`. -/
def HasLinearNeighborhoodComplexityWithConstant {n : ℕ}
    (G : SimpleGraph (Fin n)) (c : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → neighborhoodComplexity G k ≤ c * k

/-- One natural constant `c ≥ 1` bounds the neighborhood complexity of every
graph satisfying the class predicate `C` by `c · k`: the class has linear
neighborhood complexity. -/
def HasLinearNeighborhoodComplexity (C : GraphClass) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      HasLinearNeighborhoodComplexityWithConstant G c

end Lax195003.WelzlOrdersNeighborhoodComplexity
end
