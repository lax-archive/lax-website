-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic

-- Lax825748.Series
section
namespace Lax825748
end Lax825748

namespace Lax825748.Series
end Lax825748.Series
end

-- Lax825748.Monomials
section
noncomputable section

namespace Lax825748.Monomials

open Series

open scoped BigOperators

def multiFactorial {d : ℕ} (I : Fin d → ℕ) : ℕ := ∏ j, (I j).factorial

end Lax825748.Monomials
end
