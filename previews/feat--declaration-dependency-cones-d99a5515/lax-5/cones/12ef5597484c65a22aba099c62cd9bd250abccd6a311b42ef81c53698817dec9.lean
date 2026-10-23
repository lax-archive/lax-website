-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy

-- Lax12.GraphClasses
section
namespace Lax12.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax12.GraphClasses
end

-- Lax5.GraphClasses
section
namespace Lax5.GraphClasses

open scoped SimpleGraph

open Lax12.GraphClasses

/-- A graph class is weakly sparse if some complete bipartite graph
`K_{t,t}` occurs in no member as a subgraph. -/
def WeaklySparse (C : GraphClass) : Prop :=
  ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ completeBipartiteGraph (Fin t) (Fin t) ⊑ G

end Lax5.GraphClasses
end
