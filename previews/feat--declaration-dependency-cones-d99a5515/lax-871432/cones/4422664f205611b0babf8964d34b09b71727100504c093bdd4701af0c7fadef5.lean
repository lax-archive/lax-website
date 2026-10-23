-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Maps

-- Lax871432.GraphFamilies
section
namespace Lax871432.GraphFamilies

/-- An *indexed graph family* of order `n`: a family of simple graphs indexed by `ι`, the
`i`-th of which has vertex set `Fin (size i)` for some `size i ≤ n`. -/
structure GraphFamily (n : ℕ) (ι : Type*) where
  /-- The number of vertices of the `i`-th graph. -/
  size : ι → ℕ
  /-- Every graph in the family has at most `n` vertices. -/
  size_le : ∀ i, size i ≤ n
  /-- The `i`-th graph of the family. -/
  graph : ∀ i, SimpleGraph (Fin (size i))

variable {n : ℕ} {ι : Type*}

/-- Two indices carry isomorphic graphs. -/
def GraphFamily.Iso (F : GraphFamily n ι) (i j : ι) : Prop :=
  Nonempty (F.graph i ≃g F.graph j)

end Lax871432.GraphFamilies
end
