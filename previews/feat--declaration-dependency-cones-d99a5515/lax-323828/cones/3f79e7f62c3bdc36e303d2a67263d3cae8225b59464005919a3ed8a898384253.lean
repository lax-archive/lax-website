-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax323828.BooleanFourier
section
namespace Lax323828.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def character {ι : Type} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, sign (x i)

end Lax323828.BooleanFourier
end

-- Lax323828.ProductMoments
section
namespace Lax323828
end Lax323828

namespace Lax323828.ProductMoments
end Lax323828.ProductMoments
end

-- Lax323828.HigherMoments
section
namespace Lax323828.HigherMoments
end Lax323828.HigherMoments
end

-- Lax323828.EvenCovers
section
namespace Lax323828.EvenCovers

open BooleanFourier HigherMoments

open scoped BigOperators

def EvenCover {ι : Type} [DecidableEq ι] {m : ℕ} (S : Fin m → Finset ι) : Prop :=
  ∀ i, Even (Finset.univ.filter fun j ↦ i ∈ S j).card

instance decidableEvenCover {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (S : Fin m → Finset ι) : Decidable (EvenCover S) :=
  inferInstanceAs (Decidable (∀ i, Even (Finset.univ.filter fun j ↦ i ∈ S j).card))

axiom character_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (S : Fin m → Finset ι) :
  (𝔼 x : Cube ι, ∏ j, character (S j) x) =
    if EvenCover S then 1 else 0

end Lax323828.EvenCovers
end
