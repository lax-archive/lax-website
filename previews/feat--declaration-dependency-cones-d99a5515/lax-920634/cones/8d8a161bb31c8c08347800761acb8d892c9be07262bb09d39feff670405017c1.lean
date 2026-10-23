-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card

-- Lax920634.EdgeExpansion
section
namespace Lax920634.EdgeExpansion

/-- Boundary edges oriented from the set to its complement, each counted once. -/
def edgeBoundary {V : Type} (G : SimpleGraph V) (S : Set V) : Set (V × V) :=
  {e | e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2}

/-- Every vertex set of size at most half the graph has at least `h` times
its size in boundary edges. -/
def HasEdgeExpansionAtLeast {V : Type} [Fintype V]
    (G : SimpleGraph V) (h : ℚ) : Prop :=
  ∀ S : Set V, 2 * S.ncard ≤ Fintype.card V →
    h * (S.ncard : ℚ) ≤ ((edgeBoundary G S).ncard : ℚ)

end Lax920634.EdgeExpansion
end

-- Lax920634.PathReplacement
section
namespace Lax920634.PathReplacement

/-- Replace each base vertex by a path of its ports and add the paired-port edges. -/
def graph {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d) :
    SimpleGraph (Fin n × Fin d) :=
  SimpleGraph.fromRel (fun u v =>
    (u.1 = v.1 ∧ u.2.val + 1 = v.2.val) ∨ v = R u)

/-- Base boundary darts with source in `S` and target outside `S`. -/
def baseCut {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (S : Set (Fin n)) : Set (Fin n × Fin d) :=
  {p | p.1 ∈ S ∧ (R p).1 ∉ S}

end Lax920634.PathReplacement
end

-- Lax920634.PathExpansion
section
namespace Lax920634.PathExpansion

open PathReplacement EdgeExpansion Function

/-- An expanding regular port involution yields a uniformly expanding path replacement. -/
axiom replacement_expansion {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (hR : Involutive R) (hd : 2 ≤ d)
    (hbase : ∀ U : Set (Fin n),
      d * min U.ncard (n - U.ncard) ≤ 4 * (baseCut R U).ncard) :
  HasEdgeExpansionAtLeast (graph R) (1 / (8 * (d : ℚ)))

end Lax920634.PathExpansion
end
