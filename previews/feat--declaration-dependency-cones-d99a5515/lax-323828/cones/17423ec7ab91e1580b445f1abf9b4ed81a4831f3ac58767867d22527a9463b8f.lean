-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.LongCode
section
namespace Lax323828.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

end Lax323828.LongCode
end

-- Lax323828.CNASoundness
section
namespace Lax323828.CNASoundness
end Lax323828.CNASoundness
end

-- Lax323828.ManyTableConsistency
section
namespace Lax323828.ManyTableConsistency
end Lax323828.ManyTableConsistency
end

-- Lax323828.FAFTest
section
namespace Lax323828.FAFTest
end Lax323828.FAFTest
end

-- Lax323828.LongCodePatterns
section
namespace Lax323828.LongCodePatterns
end Lax323828.LongCodePatterns
end

-- Lax323828.FAFPatterns
section
namespace Lax323828.FAFPatterns

open scoped Classical

open LongCode LongCodePatterns

/-- The side condition on a larger-table word: validity and agreement with all reference answers. -/
noncomputable def conditionOfAnswers {Ω : Type} {u w q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Ω) (g : Fin q → Coordinate u) (b : Word q) : Coordinate w :=
  fun y ↦ valid ω y && decide (∀ j, g j (ρ ω y) = b j)

end Lax323828.FAFPatterns
end
