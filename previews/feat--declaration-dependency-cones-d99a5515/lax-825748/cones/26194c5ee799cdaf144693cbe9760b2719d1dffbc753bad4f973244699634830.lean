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

abbrev NCSeries (X : Type) := Word X → ℝ

abbrev NCPolynomial (X : Type) := MonoidAlgebra ℝ (Word X)

noncomputable def pairing {X : Type} (S : NCSeries X) (P : NCPolynomial X) : ℝ :=
  P.coeff.sum fun w a => a * S w

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

end Lax825748.Shuffle
end

-- Lax825748.ShuffleIdentities
section
noncomputable section

namespace Lax825748.ShuffleIdentities

open Series Shuffle LieRank Monomials

open scoped BigOperators

abbrev TensorPolynomial (X : Type) (p : ℕ) :=
  MonoidAlgebra ℝ (Fin p → Word X)

def distributions {X : Type} (p : ℕ) : List X → List (Fin p → List X)
  | [] => [fun _ => []]
  | x :: w => (distributions p w).flatMap fun v =>
      List.ofFn fun i : Fin p => Function.update v i (x :: v i)

noncomputable def coproduct {X : Type} (p : ℕ) (P : NCPolynomial X) :
    TensorPolynomial X p :=
  P.coeff.sum fun w a => ((distributions p w.toList).map fun v =>
    MonoidAlgebra.single (fun i => FreeMonoid.ofList (v i)) a).sum

noncomputable def tensorPairing {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (P : TensorPolynomial X p) : ℝ :=
  P.coeff.sum fun v a => a * ∏ i, S i (v i)

axiom pairing_coproduct {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (P : NCPolynomial X) :
  pairing (shuffleList (List.ofFn S)) P = tensorPairing S (coproduct p P)

end Lax825748.ShuffleIdentities
end
