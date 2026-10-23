-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.MvPowerSeries.Derivative

-- Lax825748.Series
section
namespace Lax825748
end Lax825748

namespace Lax825748.Series
end Lax825748.Series
end

-- Lax825748.Monomials
section
namespace Lax825748.Monomials
end Lax825748.Monomials
end

-- Lax825748.FormalSeries
section
noncomputable section

namespace Lax825748.FormalSeries

open Monomials

open scoped BigOperators

abbrev StateSeries (d : ℕ) := MvPowerSeries (Fin d) ℝ

end Lax825748.FormalSeries
end

-- Lax825748.CDA
section
noncomputable section

namespace Lax825748.CDA

open FormalSeries

def DerivativeStable {d : ℕ} (C : Subalgebra ℝ (StateSeries d)) : Prop :=
  ∀ (i : Fin d) (f : StateSeries d), f ∈ C → MvPowerSeries.pderiv ℝ i f ∈ C

def IsCDA {d : ℕ} (f : StateSeries d) : Prop :=
  ∃ C : Subalgebra ℝ (StateSeries d), C.FG ∧ DerivativeStable C ∧ f ∈ C

end Lax825748.CDA
end
