-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax12.GraphClasses
section
namespace Lax12.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax12.GraphClasses
end

-- Lax12.ColoringNumbers
section
namespace Lax12.ColoringNumbers

open scoped SimpleGraph

open Lax12.GraphClasses

/-- The set of vertices weakly `r`-reachable from `v` in `G` under the
vertex ordering `π` (vertex `u` sits at position `π u`): the endpoints
`u` of walks from `v` of length at most `r` on whose support `u` is
`π`-minimal. Contains `v` itself. -/
def wreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | ∃ w : G.Walk v u, w.length ≤ r ∧ ∀ y ∈ w.support, π u ≤ π y}

/-- The weak `r`-coloring number of `G`: the least `k` such that under
some vertex ordering every vertex weakly `r`-reaches at most `k`
vertices. -/
noncomputable def wcol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : ℕ :=
  sInf {k | ∃ π : Equiv.Perm (Fin n), ∀ v, (wreach G π r v).ncard ≤ k}

/-- Every subgraph of every member of the class, on `m` vertices, has
weak `r`-coloring number at most `c · m^ε`, where `c` depends only on
the radius `r` and on `ε > 0`: weak coloring numbers `m^{o(1)}`. -/
def HasSubpolynomialWcol (C : GraphClass) : Prop :=
  ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ⊑ G →
        (wcol H r : ℝ) ≤ c * (m : ℝ) ^ ε

end Lax12.ColoringNumbers
end
