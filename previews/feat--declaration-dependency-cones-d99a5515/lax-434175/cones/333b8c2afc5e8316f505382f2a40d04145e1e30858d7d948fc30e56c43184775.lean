-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators

-- Lax434175.Problems
section
namespace Lax434175
end Lax434175

namespace Lax434175.Problems
end Lax434175.Problems

namespace Lax434175.Problems.DecisionReduction
end Lax434175.Problems.DecisionReduction

namespace Lax434175.Problems.Embedding
end Lax434175.Problems.Embedding

namespace Lax434175.Problems.Problem
end Lax434175.Problems.Problem

namespace Lax434175.Problems.Embedding.Sound
end Lax434175.Problems.Embedding.Sound
end

-- Lax434175.MachineCovering
section
namespace Lax434175.MachineCovering

open Lax434175.Problems

structure Inst where
  jobs : ℕ
  machines : ℕ
  p : Fin jobs → ℕ

/-- The load of a machine. -/
def load (x : Inst) (σ : Fin x.jobs → Fin x.machines) (i : Fin x.machines) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), x.p j

end Lax434175.MachineCovering
end
