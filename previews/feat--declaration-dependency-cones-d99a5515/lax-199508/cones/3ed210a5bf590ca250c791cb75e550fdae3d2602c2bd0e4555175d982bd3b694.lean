-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Nat.Lattice

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
