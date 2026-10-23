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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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

open scoped BigOperators

noncomputable def gain {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W S : Submodule K V) : ℝ :=
  (Module.finrank K (W ⊔ S : Submodule K V) : ℝ)-Module.finrank K W

def Greedy {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) : Submodule K V → List ι → Prop
  | _, [] => True
  | W, i::l => (∀ j ∈ l, gain W (S j) ≤ gain W (S i)) ∧ Greedy S (W ⊔ S i) l

noncomputable def increments {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) : Submodule K V → List ι → List ℝ
  | _, [] => []
  | W, i::l => gain W (S i)::increments S (W ⊔ S i) l

end Lax342547.GreedySpans
end

-- Lax342547.ListTails
section
namespace Lax342547.ListTails
end Lax342547.ListTails
end

-- Lax342547.GreedyTails
section
namespace Lax342547.GreedyTails

open Lax342547.GreedySpans Lax342547.ListTails Lax342547.DyadicTails

open scoped BigOperators

noncomputable def deficit {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) : ℝ :=
    (l.map (fun i => gain W (S i))).sum-(increments S W l).sum

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

open Lax342547.GreedySpans Lax342547.GreedyTails

open scoped BigOperators

noncomputable def projectedDeficit {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) : ℝ :=
    (l.map (fun i => (Module.finrank K ((S i).map W.mkQ) : ℝ))).sum-
      Module.finrank K (l.toFinset.sup (fun i => (S i).map W.mkQ) : Submodule K (V ⧸ W))

axiom projected_deficit_eq {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    projectedDeficit S W l = deficit S W l

end Lax342547.ActualDeficits
end
