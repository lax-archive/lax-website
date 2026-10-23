-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Lattice

-- Lax228581.Treewidth
section
namespace Lax228581
end Lax228581

namespace Lax228581.Treewidth
end Lax228581.Treewidth

namespace Lax228581.Treewidth.TreeDecomposition
end Lax228581.Treewidth.TreeDecomposition
end

-- Lax263307.ConnectedBags
section
namespace Lax263307
end Lax263307

namespace Lax263307.ConnectedBags
end Lax263307.ConnectedBags
end

-- Lax263307.ConnectedRepresentations
section
namespace Lax263307.ConnectedRepresentations

open Lax228581.Treewidth

/-- A connected vertex set in `G` for each vertex of `H`. -/
structure Representation {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) where
  /-- The vertices used by a represented vertex. -/
  carrier : Fin t → Finset (Fin n)
  /-- Each carrier is nonempty and connected. -/
  connected : ∀ v, (G.induce (↑(carrier v) : Set (Fin n))).Connected
  /-- Carriers of adjacent vertices intersect. -/
  touching : ∀ u v, H.Adj u v → ∃ a, a ∈ carrier u ∧ a ∈ carrier v

/-- Which represented vertices use a particular host vertex. -/
def users {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    (R : Representation H G) (a : Fin n) : Finset (Fin t) :=
  Finset.univ.filter fun v => a ∈ R.carrier v

end Lax263307.ConnectedRepresentations
end
