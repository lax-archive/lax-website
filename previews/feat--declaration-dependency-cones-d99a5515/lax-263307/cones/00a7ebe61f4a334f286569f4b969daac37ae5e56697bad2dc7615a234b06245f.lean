-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Prod

-- Lax263307.Entropy
section
namespace Lax263307
end Lax263307

namespace Lax263307.Entropy
end Lax263307.Entropy
end

-- Lax263307.PathSampling
section
namespace Lax263307.PathSampling
end Lax263307.PathSampling

namespace Lax263307.PathSampling.Distribution
end Lax263307.PathSampling.Distribution
end

-- Lax263307.FiniteProductSampling
section
namespace Lax263307.FiniteProductSampling

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

noncomputable def weight (f : ι → κ → ℝ) (φ : ι → κ) : ℝ := ∏ a, f a (φ a)

axiom embedding_marginal {k : ℕ} (f : ι → κ → ℝ)
    (mass : ∀ a, (∑ x, f a x) = 1) (j : Fin k ↪ ι) (H : (Fin k → κ) → ℝ) :
    (∑ φ : ι → κ, weight f φ * H (fun a => φ (j a))) =
      ∑ ψ : Fin k → κ, weight (fun a => f (j a)) ψ * H ψ

end Lax263307.FiniteProductSampling
end
