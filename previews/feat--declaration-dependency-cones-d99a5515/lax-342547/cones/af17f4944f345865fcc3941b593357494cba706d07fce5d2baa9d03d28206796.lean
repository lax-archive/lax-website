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
import Mathlib.Tactic

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
end Lax342547.GreedySpans

namespace Lax342547.GreedySpans.Greedy
end Lax342547.GreedySpans.Greedy
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

-- Lax342547.ProjectedSpans
section
namespace Lax342547.ProjectedSpans
end Lax342547.ProjectedSpans
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

open Lax342547.SumEnvelope Lax342547.MappedSpans

open scoped BigOperators

axiom finset_span_eq {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) (I : Finset ι) :
    (⨆ i : I, S i.val) = I.sup S

end Lax342547.ListDeficits
end
