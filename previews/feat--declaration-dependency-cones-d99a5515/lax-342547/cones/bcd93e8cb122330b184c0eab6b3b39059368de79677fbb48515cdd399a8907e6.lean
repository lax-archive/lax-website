-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi

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
end Lax342547.CoverProjection
end

-- Lax342547.CoverSpace
section
namespace Lax342547.CoverSpace
end Lax342547.CoverSpace
end

-- Lax342547.PairingRank
section
namespace Lax342547.PairingRank

open Lax342547.CoverProjection

open scoped BigOperators

axiom pairing_matrix_rank_le {K V Ω : Type} [Field K] [Fintype Ω]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Submodule K V) (v : Ω → V) (hv : ∀ a, v a ∈ S) (φ : Ω → Module.Dual K V) :
    (Matrix.of (fun a b => φ b (v a))).rank ≤ Module.finrank K S

end Lax342547.PairingRank
end
