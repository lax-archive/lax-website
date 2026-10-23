-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax253009.BooleanFourier
section
namespace Lax253009
end Lax253009

namespace Lax253009.BooleanFourier
end Lax253009.BooleanFourier
end

-- Lax253009.ProductMoments
section
namespace Lax253009
end Lax253009

namespace Lax253009.ProductMoments
end Lax253009.ProductMoments
end

-- Lax253009.HigherMoments
section
namespace Lax253009.HigherMoments
end Lax253009.HigherMoments
end

-- Lax253009.EvenCovers
section
namespace Lax253009.EvenCovers

open BooleanFourier HigherMoments

open scoped BigOperators

def EvenCover {ι : Type} [DecidableEq ι] {m : ℕ} (S : Fin m → Finset ι) : Prop :=
  ∀ i, Even (Finset.univ.filter fun j ↦ i ∈ S j).card

instance decidableEvenCover {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (S : Fin m → Finset ι) : Decidable (EvenCover S) :=
  inferInstanceAs (Decidable (∀ i, Even (Finset.univ.filter fun j ↦ i ∈ S j).card))

end Lax253009.EvenCovers
end
