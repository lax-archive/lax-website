-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

-- Lax825748.Series
section
noncomputable section

namespace Lax825748.Series

abbrev Word (X : Type) := FreeMonoid X

end Lax825748.Series
end

-- Lax825748.LieRank
section
namespace Lax825748.LieRank
end Lax825748.LieRank
end

-- Lax825748.Monomials
section
namespace Lax825748.Monomials
end Lax825748.Monomials
end

-- Lax825748.Shuffle
section
namespace Lax825748.Shuffle
end Lax825748.Shuffle

namespace Lax825748.Shuffle.shuffleList
end Lax825748.Shuffle.shuffleList

namespace Lax825748.Shuffle.unshuffles
end Lax825748.Shuffle.unshuffles
end

-- Lax825748.ShuffleIdentities
section
namespace Lax825748.ShuffleIdentities.distributions
end Lax825748.ShuffleIdentities.distributions

noncomputable section

namespace Lax825748.ShuffleIdentities

open Series Shuffle LieRank Monomials

open scoped BigOperators

abbrev TensorPolynomial (X : Type) (p : ℕ) :=
  MonoidAlgebra ℝ (Fin p → Word X)

end Lax825748.ShuffleIdentities
end
