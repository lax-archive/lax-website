-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
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
end Lax263307.ConnectedRepresentations

namespace Lax263307.ConnectedRepresentations.Representation
end Lax263307.ConnectedRepresentations.Representation
end

-- Lax263307.AlmostEmbeddings
section
namespace Lax263307.AlmostEmbeddings

open scoped Classical

open Lax228581.Treewidth

/-- A connected route for every edge, disjoint for nonincident edges. -/
structure AlmostEmbedding {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) where
  /-- Vertex images, with no injectivity requirement. -/
  vertexMap : Fin t → Fin n
  /-- Host vertices on each route. -/
  route : H.edgeSet → Finset (Fin n)
  /-- Each route is nonempty and connected. -/
  connected : ∀ e, (G.induce (↑(route e) : Set (Fin n))).Connected
  /-- A route contains the images of its edge's endpoints. -/
  endpoints : ∀ e v, v ∈ e.val → vertexMap v ∈ route e
  /-- Routes of nonincident edges share no host vertex. -/
  disjoint : ∀ e f, Disjoint e.val.toFinset f.val.toFinset → Disjoint (route e) (route f)

end Lax263307.AlmostEmbeddings
end

-- Lax263307.EdgeDeletionWidth
section
namespace Lax263307
end Lax263307

namespace Lax263307.EdgeDeletionWidth
end Lax263307.EdgeDeletionWidth
end

-- Lax263307.RoutePruning
section
namespace Lax263307.RoutePruning

open scoped Classical

open AlmostEmbeddings

noncomputable def longEdges {t n : ℕ} {H : SimpleGraph (Fin t)} [DecidableRel H.Adj]
    {G : SimpleGraph (Fin n)} (E : AlmostEmbedding H G) (L : ℕ) : Finset (Sym2 (Fin t)) :=
  (Finset.univ.filter fun e : H.edgeSet => L < (E.route e).card).image Subtype.val

end Lax263307.RoutePruning
end
