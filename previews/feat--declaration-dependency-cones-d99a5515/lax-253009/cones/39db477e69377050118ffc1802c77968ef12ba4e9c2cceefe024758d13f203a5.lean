-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.LongCode
section
namespace Lax253009.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

end Lax253009.LongCode
end

-- Lax253009.CNASoundness
section
namespace Lax253009.CNASoundness
end Lax253009.CNASoundness
end

-- Lax253009.ManyTableConsistency
section
namespace Lax253009.ManyTableConsistency
end Lax253009.ManyTableConsistency
end

-- Lax253009.FAFTest
section
namespace Lax253009.FAFTest

open LongCode FiniteProbability CNASoundness

noncomputable def projected {Ω : Type} {u w : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (D : Ω → Finset (Word w)) (ω : Ω) : Finset (Word u) :=
  ((D ω).filter (fun y ↦ valid ω y = true)).image (ρ ω)

end Lax253009.FAFTest
end
