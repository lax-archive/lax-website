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

-- Lax323828.BooleanFourier
section
namespace Lax323828.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def character {ι : Type} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, sign (x i)

noncomputable def average {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) : ℝ :=
  (∑ x, F x) / (2 : ℝ) ^ Fintype.card ι

noncomputable def coefficient {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ)
    (S : Finset ι) : ℝ :=
  average fun x ↦ F x * character S x

end Lax323828.BooleanFourier
end

-- Lax323828.FourierProjection
section
namespace Lax323828.FourierProjection
end Lax323828.FourierProjection
end

-- Lax323828.SmallSupport
section
namespace Lax323828.SmallSupport

open scoped Classical

/-- The coordinate sets of size at most `l` whose squared coefficient is at least `l * δ`. -/
noncomputable def largeSets {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter fun a ↦ a.card ≤ l ∧ (l : ℝ) * δ ≤ c a ^ 2

/-- The union of the coordinate sets selected by `largeSets`. -/
noncomputable def decodingSet {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset ι :=
  (largeSets c l δ).biUnion id

end Lax323828.SmallSupport
end

-- Lax323828.FourierDecoding
section
namespace Lax323828.FourierDecoding
end Lax323828.FourierDecoding
end

-- Lax323828.FiniteProbability
section
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax323828.FiniteProbability
end

-- Lax323828.ExponentialBounds
section
namespace Lax323828.ExponentialBounds
end Lax323828.ExponentialBounds
end

-- Lax323828.BalancedPredicates
section
namespace Lax323828.BalancedPredicates

open BooleanFourier FiniteProbability

open scoped BigOperators

def predicates (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) : Finset (Cube κ) :=
  Finset.univ.filter fun B ↦ (Finset.univ.filter fun z ↦ B z = true).card = n

end Lax323828.BalancedPredicates
end

-- Lax323828.ProductMoments
section
namespace Lax323828
end Lax323828

namespace Lax323828.ProductMoments
end Lax323828.ProductMoments
end

-- Lax323828.HighDegreeSoundness
section
namespace Lax323828.HighDegreeSoundness
end Lax323828.HighDegreeSoundness
end

-- Lax323828.BalancedCancellation
section
namespace Lax323828.BalancedCancellation
end Lax323828.BalancedCancellation
end

-- Lax323828.LargeCoefficientSoundness
section
namespace Lax323828.LargeCoefficientSoundness
end Lax323828.LargeCoefficientSoundness
end

-- Lax323828.HigherMoments
section
namespace Lax323828.HigherMoments
end Lax323828.HigherMoments
end

-- Lax323828.MixedPredicateMoments
section
namespace Lax323828.MixedPredicateMoments
end Lax323828.MixedPredicateMoments
end

-- Lax323828.Hypercontractivity
section
namespace Lax323828.Hypercontractivity
end Lax323828.Hypercontractivity
end

-- Lax323828.DoubleCoverBounds
section
namespace Lax323828.DoubleCoverBounds
end Lax323828.DoubleCoverBounds
end

-- Lax323828.SmallUnionDoubleCovers
section
namespace Lax323828.SmallUnionDoubleCovers
end Lax323828.SmallUnionDoubleCovers
end

-- Lax323828.SmallCoefficientSoundness
section
namespace Lax323828.SmallCoefficientSoundness

open HighDegreeSoundness FiniteProbability

open scoped BigOperators

noncomputable def boundValue (l m r N : ℕ) (δ q : ℝ) : ℝ :=
  (∑ t ∈ Finset.range r, (2 : ℝ) ^ m * ((2 : ℝ) ^ t * δ) ^ (m - 2 * t) *
    (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t)))) +
  (1 + (3 : ℝ) ^ (l * (2 * m + 1) * 2 ^ m)) *
    (q ^ r + (2 : ℝ) ^ m * (2 * (N + 1 : ℝ) * Real.exp (-(N : ℝ) * q ^ 2 / 2)))

end Lax323828.SmallCoefficientSoundness
end

-- Lax323828.CNAPointSoundness
section
namespace Lax323828.CNAPointSoundness

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

end Lax323828.CNAPointSoundness
end
