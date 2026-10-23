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

open scoped BigOperators

noncomputable def addition {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) : (∀ i, S i) →ₗ[K] V := by
  classical
  exact LinearMap.lsum K (fun i => S i) K (fun i => (S i).subtype)

axiom addition_range {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) :
    LinearMap.range (addition S) = ⨆ i, S i

end Lax342547.SpanDeficits
end
