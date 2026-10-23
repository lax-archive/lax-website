-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax9.MergeWidth
section
namespace Lax9
end Lax9

namespace Lax9.MergeWidth
end Lax9.MergeWidth

namespace Lax9.MergeWidth.MergeSeq
end Lax9.MergeWidth.MergeSeq
end

-- Lax9.NeighborhoodComplexity
section
namespace Lax9.NeighborhoodComplexity

open Lax9.MergeWidth

open scoped Classical

universe u

variable {V : Type u} [Fintype V]

/-- The neighbourhood complexity $π_G(p)$ of a finite simple graph $G$. -/
noncomputable def neighborhoodComplexity (G : SimpleGraph V) (p : ℕ) : ℕ :=
  (Finset.univ.powersetCard p).sup fun X =>
    ((Finset.univ \ X).image fun v => X.filter fun u => G.Adj v u).card

end Lax9.NeighborhoodComplexity
end
