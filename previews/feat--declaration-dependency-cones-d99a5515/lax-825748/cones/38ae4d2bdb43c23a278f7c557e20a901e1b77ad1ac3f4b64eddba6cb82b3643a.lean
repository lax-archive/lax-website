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

abbrev NCPolynomial (X : Type) := MonoidAlgebra ℝ (Word X)

noncomputable def pairing {X : Type} (S : NCSeries X) (P : NCPolynomial X) : ℝ :=
  P.coeff.sum fun w a => a * S w

noncomputable def wordPolynomial {X : Type} (w : Word X) : NCPolynomial X :=
  MonoidAlgebra.single w 1

noncomputable def letter {X : Type} (x : X) : NCPolynomial X :=
  wordPolynomial (FreeMonoid.of x)

end Lax825748.Series
end

-- Lax825748.Monomials
section
noncomputable section

namespace Lax825748.Monomials

open Series

open scoped BigOperators

noncomputable def orderedPowers {X : Type} {d : ℕ}
    (P : Fin d → NCPolynomial X) (I : Fin d → ℕ) : NCPolynomial X :=
  (List.ofFn fun j => P j ^ I j).prod

end Lax825748.Monomials
end

-- Lax825748.FormalSeries
section
namespace Lax825748.FormalSeries
end Lax825748.FormalSeries
end

-- Lax825748.LieRank
section
noncomputable section

namespace Lax825748.LieRank

open Series

instance polynomialLieRing {X : Type} : LieRing (NCPolynomial X) :=
  LieRing.ofAssociativeRing

def liePolynomials (X : Type) : LieSubalgebra ℝ (NCPolynomial X) :=
  LieSubalgebra.lieSpan ℝ (NCPolynomial X) (Set.range letter)

abbrev LiePolynomial (X : Type) := liePolynomials X

end Lax825748.LieRank
end

-- Lax825748.PBW
section
namespace Lax825748.PBW
end Lax825748.PBW
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
namespace Lax825748.ShuffleIdentities
end Lax825748.ShuffleIdentities

namespace Lax825748.ShuffleIdentities.distributions
end Lax825748.ShuffleIdentities.distributions
end

-- Lax825748.Annihilator
section
noncomputable section

namespace Lax825748.Annihilator

open Series LieRank Monomials Shuffle ShuffleIdentities FormalSeries

abbrev LieSubalgebraOfPolynomials (X : Type) := LieSubalgebra ℝ (LiePolynomial X)

noncomputable def generatedIdeal {X : Type} (K : LieSubalgebraOfPolynomials X) :
    Ideal (NCPolynomial X) :=
  Ideal.span {P | ∃ k : K, P = k.val.val}

def InAnnihilator {X : Type} (K : LieSubalgebraOfPolynomials X) (S : NCSeries X) : Prop :=
  ∀ P ∈ generatedIdeal K, pairing S P = 0

def IsComplement {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) : Prop :=
  LinearIndependent ℝ (fun i => K.toSubmodule.mkQ (P i)) ∧
    Submodule.span ℝ (Set.range fun i => K.toSubmodule.mkQ (P i)) = ⊤

def IsCoordinateFamily {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (S : Fin d → NCSeries X) : Prop :=
  (∀ i, S i 1 = 0) ∧ (∀ i, InAnnihilator K (S i)) ∧
    ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0

def IsPBWCoordinateFamily {X : Type} {d : ℕ}
    (P : Fin d → LiePolynomial X) (S : Fin d → NCSeries X) : Prop :=
  ∀ i (I : Fin d →₀ ℕ),
    pairing (S i) (orderedPowers (fun j => (P j).val) I) =
      if I = Finsupp.single i 1 then 1 else 0

axiom coordinates_exist {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P) :
  ∃ S : Fin d → NCSeries X, IsCoordinateFamily K P S ∧ IsPBWCoordinateFamily P S

end Lax825748.Annihilator
end
