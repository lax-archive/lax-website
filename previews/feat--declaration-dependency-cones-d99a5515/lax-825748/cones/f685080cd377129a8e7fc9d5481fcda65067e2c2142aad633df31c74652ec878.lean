-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPowerSeries.Derivative

-- Lax825748.Series
section
noncomputable section

namespace Lax825748.Series

abbrev Word (X : Type) := FreeMonoid X

abbrev NCSeries (X : Type) := Word X → ℝ

end Lax825748.Series
end

-- Lax825748.Monomials
section
namespace Lax825748.Monomials
end Lax825748.Monomials
end

-- Lax825748.FormalSeries
section
namespace Lax825748.FormalSeries
end Lax825748.FormalSeries
end

-- Lax825748.ConvergentSeries
section
namespace Lax825748.ConvergentSeries
end Lax825748.ConvergentSeries
end

-- Lax825748.DifferentialRepresentation
section
namespace Lax825748.DifferentialRepresentation
end Lax825748.DifferentialRepresentation

namespace Lax825748.DifferentialRepresentation.Representation
end Lax825748.DifferentialRepresentation.Representation
end

-- Lax825748.AnalyticRepresentations
section
namespace Lax825748.AnalyticRepresentations
end Lax825748.AnalyticRepresentations
end

-- Lax825748.FactorialEstimate
section
noncomputable section

namespace Lax825748.FactorialEstimate

open Lax825748.Series Lax825748.DifferentialRepresentation

open ConvergentSeries AnalyticRepresentations

def HasFactorialBound {X : Type} (g : NCSeries X) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ ∀ w : Word X,
    |g w| ≤ α * C ^ w.toList.length * (w.toList.length.factorial : ℝ)

end Lax825748.FactorialEstimate
end
