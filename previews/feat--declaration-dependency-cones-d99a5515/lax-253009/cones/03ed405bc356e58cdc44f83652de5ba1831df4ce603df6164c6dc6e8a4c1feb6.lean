-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

-- Lax253009.BooleanFourier
section
namespace Lax253009.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def character {ι : Type} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, sign (x i)

noncomputable def average {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) : ℝ :=
  (∑ x, F x) / (2 : ℝ) ^ Fintype.card ι

noncomputable def coefficient {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ)
    (S : Finset ι) : ℝ :=
  average fun x ↦ F x * character S x

end Lax253009.BooleanFourier
end

-- Lax253009.FourierProjection
section
namespace Lax253009.FourierProjection
end Lax253009.FourierProjection
end

-- Lax253009.SmallSupport
section
namespace Lax253009.SmallSupport

noncomputable def largeSets {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter fun a ↦ a.card ≤ l ∧ (l : ℝ) * δ ≤ c a ^ 2

noncomputable def decodingSet {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset ι :=
  (largeSets c l δ).biUnion id

end Lax253009.SmallSupport
end

-- Lax253009.FourierDecoding
section
namespace Lax253009.FourierDecoding
end Lax253009.FourierDecoding
end

-- Lax253009.FiniteProbability
section
namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax253009.FiniteProbability
end

-- Lax253009.ExponentialBounds
section
namespace Lax253009.ExponentialBounds
end Lax253009.ExponentialBounds
end

-- Lax253009.BalancedPredicates
section
namespace Lax253009.BalancedPredicates

open BooleanFourier FiniteProbability

open scoped BigOperators

def predicates (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) : Finset (Cube κ) :=
  Finset.univ.filter fun B ↦ (Finset.univ.filter fun z ↦ B z = true).card = n

end Lax253009.BalancedPredicates
end

-- Lax253009.ProductMoments
section
namespace Lax253009
end Lax253009

namespace Lax253009.ProductMoments
end Lax253009.ProductMoments
end

-- Lax253009.HighDegreeSoundness
section
namespace Lax253009.HighDegreeSoundness
end Lax253009.HighDegreeSoundness
end

-- Lax253009.BalancedCancellation
section
namespace Lax253009.BalancedCancellation
end Lax253009.BalancedCancellation
end

-- Lax253009.LargeCoefficientSoundness
section
namespace Lax253009.LargeCoefficientSoundness
end Lax253009.LargeCoefficientSoundness
end

-- Lax253009.HigherMoments
section
namespace Lax253009.HigherMoments
end Lax253009.HigherMoments
end

-- Lax253009.MixedPredicateMoments
section
namespace Lax253009.MixedPredicateMoments
end Lax253009.MixedPredicateMoments
end

-- Lax253009.Hypercontractivity
section
namespace Lax253009.Hypercontractivity
end Lax253009.Hypercontractivity
end

-- Lax253009.DoubleCoverBounds
section
namespace Lax253009.DoubleCoverBounds
end Lax253009.DoubleCoverBounds
end

-- Lax253009.SmallUnionDoubleCovers
section
namespace Lax253009.SmallUnionDoubleCovers
end Lax253009.SmallUnionDoubleCovers
end

-- Lax253009.SmallCoefficientSoundness
section
namespace Lax253009.SmallCoefficientSoundness

open HighDegreeSoundness FiniteProbability

open scoped BigOperators

noncomputable def boundValue (l m r N : ℕ) (δ q : ℝ) : ℝ :=
  (∑ t ∈ Finset.range r, (2 : ℝ) ^ m * ((2 : ℝ) ^ t * δ) ^ (m - 2 * t) *
    (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t)))) +
  (1 + (3 : ℝ) ^ (l * (2 * m + 1) * 2 ^ m)) *
    (q ^ r + (2 : ℝ) ^ m * (2 * (N + 1 : ℝ) * Real.exp (-(N : ℝ) * q ^ 2 / 2)))

end Lax253009.SmallCoefficientSoundness
end

-- Lax253009.CNAPointSoundness
section
namespace Lax253009.CNAPointSoundness

open BooleanFourier BalancedPredicates FiniteProbability

noncomputable def decoding {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l : ℕ) (τ : ℝ) : Finset ι :=
  SmallSupport.decodingSet (coefficient F) l (τ ^ 2 / l)

def Matches {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (F : Cube ι → ℝ) (n : ℕ) (f : ι → κ) (y : ι) : Prop :=
  ∀ B : predicates κ n, F (fun i ↦ B.val (f i)) = sign (B.val (f y))

def Avoids {ι κ : Type} (D : Finset ι) (f : ι → κ) (y : ι) : Prop :=
  ∀ x ∈ D, f x ≠ f y

noncomputable def pointBound (l m r N : ℕ) (τ q : ℝ) : ℝ :=
  9 * (q ^ l + 2 * (N + 1 : ℝ) * Real.exp (-(N : ℝ) * q ^ 2 / 2)) +
    (3 : ℝ) ^ m * SmallCoefficientSoundness.boundValue l m r N τ q

axiom point_soundness {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1)
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (l m r : ℕ) (hl : 0 < l) (hlN : l < Fintype.card κ)
    (τ q : ℝ) (hτ : 0 < τ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 2 * r ≤ m) (hm : Even m)
    (hlarge : (l : ℝ) / ((Fintype.card κ : ℝ) - l) / τ ≤ 1 / 3)
    (y : ι) :
  probability (fun f : ι → κ ↦ Matches F n f y ∧ Avoids (decoding F l τ) f y) ≤
    pointBound l m r (Fintype.card κ) τ q

end Lax253009.CNAPointSoundness
end
