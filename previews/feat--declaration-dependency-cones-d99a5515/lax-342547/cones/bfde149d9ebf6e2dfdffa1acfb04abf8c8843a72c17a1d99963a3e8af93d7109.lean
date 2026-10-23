-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
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

noncomputable def increments {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) : Submodule K V → List ι → List ℝ
  | _, [] => []
  | W, i::l => gain W (S i)::increments S (W ⊔ S i) l

axiom increments_sum {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    (increments S W l).sum = (Module.finrank K (spanAfter S W l) : ℝ)-Module.finrank K W

end Lax342547.GreedySpans
end
