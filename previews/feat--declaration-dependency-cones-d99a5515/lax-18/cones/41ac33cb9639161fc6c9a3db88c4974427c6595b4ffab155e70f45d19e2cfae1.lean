-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

-- Lax18.EdgeDensity
section
namespace Lax18
end Lax18

namespace Lax18.EdgeDensity
end Lax18.EdgeDensity
end

-- Lax18.RegularPairs
section
namespace Lax18.RegularPairs

open Lax18.EdgeDensity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `X` is a large enough subset of `A` for the threshold `ε`. -/
def LargeSubset (ε : ℝ) (A X : Finset V) : Prop :=
  X ⊆ A ∧ ε * (A.card : ℝ) ≤ (X.card : ℝ)

end Lax18.RegularPairs
end
