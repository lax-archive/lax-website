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

end Lax825748.Series
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

-- Lax825748.Monomials
section
noncomputable section

namespace Lax825748.Monomials

open Series

open scoped BigOperators

def totalDegree {d : ℕ} (I : Fin d → ℕ) : ℕ := ∑ j, I j

def multiFactorial {d : ℕ} (I : Fin d → ℕ) : ℕ := ∏ j, (I j).factorial

noncomputable def orderedPowers {X : Type} {d : ℕ}
    (P : Fin d → NCPolynomial X) (I : Fin d → ℕ) : NCPolynomial X :=
  (List.ofFn fun j => P j ^ I j).prod

end Lax825748.Monomials
end

-- Lax825748.ConvergenceHypothesis
section
noncomputable section

namespace Lax825748.ConvergenceHypothesis

open Lax825748.Series Lax825748.LieRank Lax825748.Monomials

def Holds {X : Type} (g : NCSeries X) : Prop :=
  ∀ (q : ℕ) (P : Fin q → LiePolynomial X),
    ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧
      ∀ I : Fin q → ℕ,
        |pairing g (orderedPowers (fun j => (P j).val) I)| ≤
          α * C ^ totalDegree I * (multiFactorial I : ℝ)

end Lax825748.ConvergenceHypothesis
end

-- Lax825748.ResidualConvergence
section
noncomputable section

namespace Lax825748.ResidualConvergence

open Lax825748.Series ConvergenceHypothesis

axiom right_residual {X : Type} (g : NCSeries X) (hg : Holds g)
    (Q : NCPolynomial X) :
  Holds (rightResidual g Q)

end Lax825748.ResidualConvergence
end
