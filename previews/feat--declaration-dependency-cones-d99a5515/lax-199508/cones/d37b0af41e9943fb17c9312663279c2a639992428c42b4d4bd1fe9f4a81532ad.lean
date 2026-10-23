-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

-- Lax199508.ShallowTopologicalMinors
section
namespace Lax199508.ShallowTopologicalMinors

/-- A model of `H` as a depth-`r` topological minor of `G`: an injective
choice of a principal vertex of `G` for each vertex of `H`, together
with a connecting walk of length at most `2 * r + 1` for each edge of
`H`, where the walks pass through no principal vertex other than those
of their own two endpoints and meet each other only in principal
vertices. -/
structure ShallowTopologicalMinorModel {V W : Type*} (r : ℕ) (H : SimpleGraph W)
    (G : SimpleGraph V) where
  /-- The principal vertex of `G` realizing each vertex of `H`. -/
  principal : W → V
  /-- Distinct vertices of `H` have distinct principal vertices. -/
  principal_inj : Function.Injective principal
  /-- The walk of `G` connecting the principal vertices of an edge of
  `H`. -/
  walk : ∀ (u v : W), H.Adj u v → G.Walk (principal u) (principal v)
  /-- Connecting walks have length at most `2 * r + 1`: they subdivide
  the edge at most `2 * r` times. -/
  length_le : ∀ (u v : W) (h : H.Adj u v), (walk u v h).length ≤ 2 * r + 1
  /-- A principal vertex lying on a connecting walk is one of the two
  endpoints of that edge. -/
  principal_eq : ∀ (u v : W) (h : H.Adj u v) (w : W),
    principal w ∈ (walk u v h).support → w = u ∨ w = v
  /-- Connecting walks meet only in principal vertices: a vertex lying
  on two connecting walks and on none of the principal vertices forces
  the two edges to agree. -/
  disjoint : ∀ (u v : W) (h : H.Adj u v) (u' v' : W) (h' : H.Adj u' v') (x : V),
    x ∈ (walk u v h).support → x ∈ (walk u' v' h').support →
      x ∉ Set.range principal → (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')

end Lax199508.ShallowTopologicalMinors
end
