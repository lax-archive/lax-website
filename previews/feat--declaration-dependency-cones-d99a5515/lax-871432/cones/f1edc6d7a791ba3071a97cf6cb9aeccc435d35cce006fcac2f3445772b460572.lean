-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.SetTheory.Cardinal.Finite

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

end Lax871432.GraphFamilies
end

-- Lax871432.HomomorphismCounts
section
namespace Lax871432.HomomorphismCounts

/-- $\hom(F, G)$, the number of homomorphisms from `F` to `G`. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card (F →g G)

end Lax871432.HomomorphismCounts
end

-- Lax871432.LovaszTheorem
section
open Lax871432.GraphFamilies Lax871432.HomomorphismCounts

namespace Lax871432.LovaszTheorem

variable {n : ℕ} {ι : Type*}

/-- The *homomorphism matrix* of a graph family, `M i j = hom(F i, F j)`. -/
noncomputable def homMatrix (F : GraphFamily n ι) : Matrix ι ι ℚ :=
  Matrix.of fun i j => (homCount (F.graph i) (F.graph j) : ℚ)

end Lax871432.LovaszTheorem
end
