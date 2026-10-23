-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

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

-- Lax263307.RoutingNormalization
section
namespace Lax263307.RoutingNormalization

open scoped Classical

def IsUniquePair {n q : ℕ} (E : Fin n → Fin n → Fin q → Prop) : Prop :=
  ∀ i u v u' v', E u v i → E u' v' i → u = u' ∧ v = v'

noncomputable def routed {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (u v : Fin n) : ℝ :=
  ∑ i, if E u v i then w i else 0

noncomputable def probability {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (u v : Fin n) (i : Fin q) : ℝ :=
  if E u v i then w i / (routed w E u v * (n : ℝ) ^ 2) else 0

/-- Uniform commodity normalization preserves the scaled load bound. -/
axiom normalized_load_bound {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (hn : 0 < n)
    (nonnegative : ∀ i, 0 ≤ w i) (unique : IsUniquePair E)
    (γ : ℝ) (γ_positive : 0 < γ) (lower_bound : ∀ u v, 1 / γ ≤ routed w E u v)
    (cost : Fin q → ℝ) (cost_nonnegative : ∀ i, 0 ≤ cost i) :
    (∑ u, ∑ v, ∑ i, probability w E u v i * cost i) ≤
      γ / (n : ℝ) ^ 2 * (∑ i, w i * cost i)

end Lax263307.RoutingNormalization
end
