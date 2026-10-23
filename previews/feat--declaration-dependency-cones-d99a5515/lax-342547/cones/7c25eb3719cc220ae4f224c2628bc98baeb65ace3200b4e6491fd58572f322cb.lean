-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.MixtureRecovery
section
namespace Lax342547.MixtureRecovery
end Lax342547.MixtureRecovery
end

-- Lax342547.MomentSpace
section
namespace Lax342547
end Lax342547

namespace Lax342547.MomentSpace
end Lax342547.MomentSpace

namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh
end Lax342547.Walsh
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh
end Lax342547.PushforwardWalsh
end

-- Lax342547.RetainedImages
section
namespace Lax342547.RetainedImages
end Lax342547.RetainedImages
end

-- Lax342547.RealCellLaws
section
namespace Lax342547.RealCellLaws
end Lax342547.RealCellLaws
end

-- Lax342547.PairRecovery
section
namespace Lax342547.PairRecovery

open Lax342547.RealCellLaws

open scoped ENNReal

noncomputable def independentPair {ΩA ΩB : Type} (p : PMF ΩA) (q : PMF ΩB) : PMF (ΩA × ΩB) :=
  p.bind (fun a => q.map (fun b => (a,b)))

end Lax342547.PairRecovery
end

-- Lax342547.IndependentMixtures
section
namespace Lax342547.IndependentMixtures

open Lax342547.PairRecovery

open scoped ENNReal

axiom independent_pair_mixture {ΩA ΩB J K : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype J] [Fintype K]
    (p : J → PMF ΩA) (q : K → PMF ΩB) (p₀ : PMF ΩA) (q₀ : PMF ΩB)
    (w : J → ℝ≥0∞) (v : K → ℝ≥0∞)
    (hp : ∀ a, p₀ a = ∑ j, w j * p j a) (hq : ∀ b, q₀ b = ∑ k, v k * q k b)
    (ab : ΩA × ΩB) :
    independentPair p₀ q₀ ab = ∑ jk : J × K, (w jk.1 * v jk.2) * independentPair (p jk.1) (q jk.2) ab

end Lax342547.IndependentMixtures
end
