-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

-- Lax825748.Series
section
namespace Lax825748
end Lax825748

namespace Lax825748.Series
end Lax825748.Series
end

-- Lax825748.LieRank
section
namespace Lax825748.LieRank
end Lax825748.LieRank
end

-- Lax825748.Monomials
section
noncomputable section

namespace Lax825748.Monomials

open Series

open scoped BigOperators

def totalDegree {d : ℕ} (I : Fin d → ℕ) : ℕ := ∑ j, I j

def multiFactorial {d : ℕ} (I : Fin d → ℕ) : ℕ := ∏ j, (I j).factorial

end Lax825748.Monomials
end

-- Lax825748.ConvergenceHypothesis
section
noncomputable section

namespace Lax825748.ConvergenceHypothesis

open Lax825748.Series Lax825748.LieRank Lax825748.Monomials

axiom factorial_comparison {q : ℕ} (I : Fin q → ℕ) :
  multiFactorial I ≤ (totalDegree I).factorial ∧
    (totalDegree I).factorial ≤ q ^ totalDegree I * multiFactorial I

end Lax825748.ConvergenceHypothesis
end
