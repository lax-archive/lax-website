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
import Mathlib.LinearAlgebra.Span.Defs

-- Lax825748.Series
section
noncomputable section

namespace Lax825748.Series

abbrev Word (X : Type) := FreeMonoid X

abbrev NCSeries (X : Type) := Word X → ℝ

abbrev NCPolynomial (X : Type) := MonoidAlgebra ℝ (Word X)

noncomputable def pairing {X : Type} (S : NCSeries X) (P : NCPolynomial X) : ℝ :=
  P.coeff.sum fun w a => a * S w

noncomputable def wordPolynomial {X : Type} (w : Word X) : NCPolynomial X :=
  MonoidAlgebra.single w 1

noncomputable def letter {X : Type} (x : X) : NCPolynomial X :=
  wordPolynomial (FreeMonoid.of x)

noncomputable def rightResidual {X : Type} (S : NCSeries X)
    (P : NCPolynomial X) : NCSeries X :=
  fun w => pairing S (P * wordPolynomial w)

noncomputable def constantSeries {X : Type} (a : ℝ) : NCSeries X := by
  classical
  exact fun w => if w = 1 then a else 0

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
namespace Lax825748.Shuffle.shuffleList
end Lax825748.Shuffle.shuffleList

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

end Lax825748.Shuffle
end

-- Lax825748.ShuffleIdentities
section
namespace Lax825748.ShuffleIdentities
end Lax825748.ShuffleIdentities

namespace Lax825748.ShuffleIdentities.distributions
end Lax825748.ShuffleIdentities.distributions
end

-- Lax825748.ShuffleFinite
section
noncomputable section

namespace Lax825748.ShuffleFinite

open Series Shuffle ShuffleIdentities

structure ShuffleSubalgebra (X : Type) where
  toSubmodule : Submodule ℝ (NCSeries X)
  one_mem : constantSeries 1 ∈ toSubmodule
  shuffle_mem : ∀ S T, S ∈ toSubmodule → T ∈ toSubmodule → shuffle S T ∈ toSubmodule

def DerivativeStable {X : Type} (A : ShuffleSubalgebra X) : Prop :=
  ∀ (x : X) (T : NCSeries X), T ∈ A.toSubmodule →
    rightResidual T (letter x) ∈ A.toSubmodule

end Lax825748.ShuffleFinite
end
