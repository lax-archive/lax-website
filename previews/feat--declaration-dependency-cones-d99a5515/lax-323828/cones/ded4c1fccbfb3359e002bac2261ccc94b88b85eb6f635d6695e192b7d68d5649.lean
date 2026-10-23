-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax323828.BooleanFourier
section
namespace Lax323828.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

end Lax323828.BooleanFourier
end

-- Lax323828.FourierIdentities
section
namespace Lax323828.FourierIdentities

open BooleanFourier

open scoped symmDiff

def bitFlip {ι : Type} (x : Cube ι) : Cube ι := fun i ↦ !(x i)

end Lax323828.FourierIdentities
end
