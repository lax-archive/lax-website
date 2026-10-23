-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.DirectRanks
section
namespace Lax342547.DirectRanks

open scoped BigOperators

axiom diagonal_rank_sum {K ι : Type} [Field K] [Fintype ι]
    {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)] (M : ∀ i, V i →ₗ[K] W i) :
    Module.finrank K (LinearMap.range (LinearMap.piMap M)) =
      ∑ i, Module.finrank K (LinearMap.range (M i))

end Lax342547.DirectRanks
end
