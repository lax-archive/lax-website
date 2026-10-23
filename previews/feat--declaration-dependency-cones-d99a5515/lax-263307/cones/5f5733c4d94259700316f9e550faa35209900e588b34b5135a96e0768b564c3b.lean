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

-- Lax263307.RepeatedCutAccounting
section
namespace Lax263307.RepeatedCutAccounting

noncomputable def cost {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ v ∈ S, x v

axiom total_cut_cost {n q : ℕ} (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v)
    (A B : Fin q → Finset (Fin n)) (disjoint : Pairwise fun i j => Disjoint (B i) (B j))
    (ρ γ : ℝ) (rho_nonnegative : 0 ≤ ρ) (gamma_positive : 0 < γ)
    (each_cut : ∀ i, cost x (A i ∩ B i) ≤ 4 * ρ * (A i).card * (B i).card / γ) :
    cost x (Finset.univ.biUnion fun i => A i ∩ B i) ≤ 4 * ρ * (n : ℝ) ^ 2 / γ

end Lax263307.RepeatedCutAccounting
end
