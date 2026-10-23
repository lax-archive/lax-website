-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
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
end Lax342547.DirectRanks
end

-- Lax342547.QuotientRank
section
namespace Lax342547.QuotientRank
end Lax342547.QuotientRank
end

-- Lax342547.RankLoss
section
namespace Lax342547.RankLoss
end Lax342547.RankLoss
end

-- Lax342547.SpanDeficits
section
namespace Lax342547.SpanDeficits

open scoped BigOperators

noncomputable def addition {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) : (∀ i, S i) →ₗ[K] V := by
  classical
  exact LinearMap.lsum K (fun i => S i) K (fun i => (S i).subtype)

end Lax342547.SpanDeficits
end

-- Lax342547.BlockDeficits
section
namespace Lax342547.BlockDeficits

open Lax342547.SpanDeficits

open scoped BigOperators

noncomputable def liftedSum {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : ι → Submodule K W) (T : ι → Submodule K V)
    (M : ∀ i, Module.Dual K (T i) →ₗ[K] S i) : Module.Dual K V →ₗ[K] W := by
  classical
  let B := (LinearMap.lsum K (fun i => T i) K).symm.toLinearMap.comp (addition T).dualMap
  exact (addition S).comp ((LinearMap.piMap M).comp B)

end Lax342547.BlockDeficits
end

-- Lax342547.LiftedSum
section
namespace Lax342547.LiftedSum

open Lax342547.SpanDeficits Lax342547.BlockDeficits

open scoped BigOperators

axiom lifted_sum_apply {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : ι → Submodule K W) (T : ι → Submodule K V)
    (M : ∀ i, Module.Dual K (T i) →ₗ[K] S i) (f : Module.Dual K V) :
    liftedSum S T M f = ∑ i, (M i ((T i).subtype.dualMap f)).val

end Lax342547.LiftedSum
end
