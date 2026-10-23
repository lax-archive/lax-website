-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

-- Lax12.GraphClasses
section
namespace Lax12
end Lax12

namespace Lax12.GraphClasses
end Lax12.GraphClasses
end

-- Lax12.UniformQuasiWideness
section
namespace Lax12.UniformQuasiWideness

open Lax12.GraphClasses

/-- A set of vertices is distance-`r` independent in `G` when every walk
between two distinct members is longer than `r`. -/
def DistIndependent {V : Type*} (G : SimpleGraph V) (r : ℕ) (A : Set V) : Prop :=
  A.Pairwise fun u v => ∀ p : G.Walk u v, r < p.length

end Lax12.UniformQuasiWideness
end
