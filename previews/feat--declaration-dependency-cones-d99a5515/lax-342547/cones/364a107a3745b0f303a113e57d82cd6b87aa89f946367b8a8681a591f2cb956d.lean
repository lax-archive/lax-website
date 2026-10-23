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

-- Lax342547.SpanDeficits
section
namespace Lax342547.SpanDeficits
end Lax342547.SpanDeficits
end

-- Lax342547.SpanDeficitMono
section
namespace Lax342547.SpanDeficitMono

open Lax342547.SpanDeficits

open scoped BigOperators

axiom deficit_monotone {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S T : ι → Submodule K V) (h : ∀ i, S i ≤ T i) :
    ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K V)) ≤
      ((∑ i, Module.finrank K (T i))-Module.finrank K (⨆ i, T i : Submodule K V))

end Lax342547.SpanDeficitMono
end
