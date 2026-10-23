-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.BernoulliSampling
section
namespace Lax323828.BernoulliSampling

open scoped Classical

open FiniteProbability

/-- Count how many of the sampled points satisfy the event `P`. -/
noncomputable def count {Ω : Type} [Fintype Ω] (N : ℕ) (P : Ω → Prop)
    (z : Fin N → Ω) : ℕ :=
  (Finset.univ.filter (fun i ↦ P (z i))).card

end Lax323828.BernoulliSampling
end
