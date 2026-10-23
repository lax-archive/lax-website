-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.SpanDeficits
section
namespace Lax342547.SpanDeficits
end Lax342547.SpanDeficits
end

-- Lax342547.GreedySpans
section
namespace Lax342547.GreedySpans

open scoped BigOperators

noncomputable def gain {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W S : Submodule K V) : ℝ :=
  (Module.finrank K (W ⊔ S : Submodule K V) : ℝ)-Module.finrank K W

def Greedy {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) : Submodule K V → List ι → Prop
  | _, [] => True
  | W, i::l => (∀ j ∈ l, gain W (S j) ≤ gain W (S i)) ∧ Greedy S (W ⊔ S i) l

noncomputable def spanAfter {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (S : ι → Submodule K V) : Submodule K V → List ι → Submodule K V
  | W, [] => W
  | W, i::l => spanAfter S (W ⊔ S i) l

end Lax342547.GreedySpans
end

-- Lax342547.ProjectedSpans
section
namespace Lax342547.ProjectedSpans
end Lax342547.ProjectedSpans
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

-- Lax342547.CoverProjection
section
namespace Lax342547.CoverProjection

open Lax342547.GreedySpans

open scoped BigOperators

noncomputable def projection {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    T.dualCoannihilator →ₗ[K] (W ⧸ S) := S.mkQ.comp (M.comp T.dualCoannihilator.subtype)

end Lax342547.CoverProjection
end

-- Lax342547.DyadicDeficits
section
namespace Lax342547
end Lax342547

namespace Lax342547.DyadicDeficits
end Lax342547.DyadicDeficits
end

-- Lax342547.DyadicTails
section
namespace Lax342547.DyadicTails
end Lax342547.DyadicTails
end

-- Lax342547.DyadicScale
section
namespace Lax342547.DyadicScale
end Lax342547.DyadicScale
end

-- Lax342547.ListTails
section
namespace Lax342547.ListTails
end Lax342547.ListTails
end

-- Lax342547.GreedyTails
section
namespace Lax342547.GreedyTails
end Lax342547.GreedyTails
end

-- Lax342547.ActualDeficits
section
namespace Lax342547.ActualDeficits
end Lax342547.ActualDeficits
end

-- Lax342547.MappedSpans
section
namespace Lax342547.MappedSpans
end Lax342547.MappedSpans
end

-- Lax342547.SpanDeficitMono
section
namespace Lax342547.SpanDeficitMono
end Lax342547.SpanDeficitMono
end

-- Lax342547.DirectRanks
section
namespace Lax342547.DirectRanks
end Lax342547.DirectRanks
end

-- Lax342547.BlockDeficits
section
namespace Lax342547.BlockDeficits
end Lax342547.BlockDeficits
end

-- Lax342547.SumRank
section
namespace Lax342547.SumRank
end Lax342547.SumRank
end

-- Lax342547.SumEnvelope
section
namespace Lax342547.SumEnvelope
end Lax342547.SumEnvelope
end

-- Lax342547.ListDeficits
section
namespace Lax342547.ListDeficits
end Lax342547.ListDeficits
end

-- Lax342547.CombinedSpans
section
namespace Lax342547.CombinedSpans
end Lax342547.CombinedSpans
end

-- Lax342547.SmallExposure
section
namespace Lax342547.SmallExposure
end Lax342547.SmallExposure
end

-- Lax342547.PartitionLists
section
namespace Lax342547.PartitionLists
end Lax342547.PartitionLists
end

-- Lax342547.ExposedSums
section
namespace Lax342547.ExposedSums

open Lax342547.GreedySpans Lax342547.CoverProjection

open scoped BigOperators

axiom remaining_projection_sum {K V W ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : ι → V →ₗ[K] W) (l : List ι) (hl : l.Nodup) (hI : l.toFinset = Finset.univ) (t : ℕ) :
    let S := spanAfter (fun i => LinearMap.range (M i)) ⊥ (l.take t)
    let T := spanAfter (fun i => LinearMap.range (M i).dualMap) ⊥ (l.take t)
    projection (∑ i : (l.drop t).toFinset, M i.val) S T = projection (∑ i, M i) S T

end Lax342547.ExposedSums
end
