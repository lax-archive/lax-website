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
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPowerSeries.Derivative

-- Lax825748.Series
section
noncomputable section

namespace Lax825748.Series

abbrev Word (X : Type) := FreeMonoid X

abbrev NCSeries (X : Type) := Word X → ℝ

noncomputable def constantSeries {X : Type} (a : ℝ) : NCSeries X := by
  classical
  exact fun w => if w = 1 then a else 0

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

-- Lax825748.LieRank
section
namespace Lax825748.LieRank
end Lax825748.LieRank
end

-- Lax825748.PBW
section
namespace Lax825748.PBW
end Lax825748.PBW
end

-- Lax825748.Shuffle
section
noncomputable section

namespace Lax825748.Shuffle

open Series

def unshuffles {X : Type} : List X → List (List X × List X)
  | [] => [([], [])]
  | x :: w => (unshuffles w).flatMap fun p =>
      [(x :: p.1, p.2), (p.1, x :: p.2)]

noncomputable def shuffle {X : Type} (S T : NCSeries X) : NCSeries X :=
  fun w => ((unshuffles w.toList).map fun p =>
    S (FreeMonoid.ofList p.1) * T (FreeMonoid.ofList p.2)).sum

noncomputable def shuffleList {X : Type} : List (NCSeries X) → NCSeries X
  | [] => constantSeries 1
  | S :: l => shuffle S (shuffleList l)

noncomputable def shufflePow {X : Type} (S : NCSeries X) (n : ℕ) : NCSeries X :=
  shuffleList (List.replicate n S)

end Lax825748.Shuffle
end

-- Lax825748.ShuffleIdentities
section
namespace Lax825748.ShuffleIdentities.distributions
end Lax825748.ShuffleIdentities.distributions

noncomputable section

namespace Lax825748.ShuffleIdentities

open Series Shuffle LieRank Monomials

open scoped BigOperators

noncomputable def shuffleMonomial {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (I : Fin d → ℕ) : NCSeries X :=
  shuffleList (List.ofFn fun i => shufflePow (S i) (I i))

end Lax825748.ShuffleIdentities
end

-- Lax825748.Annihilator
section
noncomputable section

namespace Lax825748.Annihilator

open Series LieRank Monomials Shuffle ShuffleIdentities FormalSeries

noncomputable def substituteShuffle {X : Type} {d : ℕ}
    (S : Fin d → NCSeries X) (f : StateSeries d) : NCSeries X :=
  fun w => (AddMonoidAlgebra.coeff
    (MvPowerSeries.truncTotal (w.toList.length + 1) f)).sum
    fun I a => a * shuffleMonomial S I w

end Lax825748.Annihilator
end
