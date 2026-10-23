-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax199508.GraphClasses
section
namespace Lax199508
end Lax199508

namespace Lax199508.GraphClasses
end Lax199508.GraphClasses
end

-- Lax199508.Admissibility
section
namespace Lax199508.Admissibility

open Lax199508.GraphClasses

/-- An admissible family of `k` paths at `v` under the ordering `π`:
`k` walks of length at most `r` out of `v`, each ending strictly before
`v` in the ordering, pairwise meeting only in `v`. -/
structure AdmFamily {n : ℕ} (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) (r k : ℕ) (v : Fin n) where
  /-- The endpoint of each path. -/
  target : Fin k → Fin n
  /-- The path from `v` to each endpoint. -/
  path : ∀ i, G.Walk v (target i)
  /-- Every endpoint comes strictly before `v` in the ordering. -/
  target_lt : ∀ i, π (target i) < π v
  /-- Every path has length at most `r`. -/
  length_le : ∀ i, (path i).length ≤ r
  /-- Distinct paths meet only in `v`. -/
  meet_eq : ∀ i j, i ≠ j → ∀ y ∈ (path i).support,
    y ∈ (path j).support → y = v

/-- Some vertex ordering admits no admissible family of `k` paths at any
vertex: the `r`-admissibility is at most `k`. -/
def HasAdmAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ) : Prop :=
  ∃ π : Equiv.Perm (Fin n), ∀ (v : Fin n) (j : ℕ),
    Nonempty (AdmFamily G π r j v) → j + 1 ≤ k

/-- The `r`-admissibility of `G`: the least bound achieved by some
vertex ordering. -/
noncomputable def adm {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | HasAdmAtMost G r k}

end Lax199508.Admissibility
end

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

/-- `H` is a topological minor of `G` at depth `r`. -/
def HasShallowTopologicalMinor {V W : Type*} (G : SimpleGraph V) (r : ℕ)
    (H : SimpleGraph W) : Prop :=
  Nonempty (ShallowTopologicalMinorModel r H G)

/-- Every depth-`r` topological minor of `G`, on `m` vertices, has at
most `d · m` edges. -/
def HasTopologicalDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (r d : ℕ) :
    Prop :=
  ∀ (m : ℕ) (H : SimpleGraph (Fin m)), HasShallowTopologicalMinor G r H →
    H.edgeSet.ncard ≤ d * m

end Lax199508.ShallowTopologicalMinors
end

-- Lax199508.AdmissibilityBound
section
namespace Lax199508.AdmissibilityBound

open Lax199508.Admissibility Lax199508.ShallowTopologicalMinors

/-- A depth-`r` topological edge-density bound `d` for `G` bounds the
`(r+1)`-admissibility of `G` by `1 + 6 · (r+1) · d ^ 3`. -/
axiom adm_le_of_hasTopologicalDensityAtMost {n : ℕ} (G : SimpleGraph (Fin n))
    (r d : ℕ) (h : HasTopologicalDensityAtMost G r d) :
    adm G (r + 1) ≤ 1 + 6 * (r + 1) * d ^ 3

end Lax199508.AdmissibilityBound
end
