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

open Lax342547.RetainedImages Lax342547.PushforwardWalsh

open scoped ENNReal

noncomputable def weights {Ω : Type} (p : PMF Ω) : Ω → ℝ := fun ω => (p ω).toReal

end Lax342547.RealCellLaws
end

-- Lax342547.PairRecovery
section
namespace Lax342547.PairRecovery

open Lax342547.RealCellLaws

open scoped ENNReal

noncomputable def pairMass {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (H : ΩA → ΩB → Prop) : ℝ := by
  classical
  exact ∑ a, ∑ b, if H a b then α a * β b else 0

noncomputable def independentPair {ΩA ΩB : Type} (p : PMF ΩA) (q : PMF ΩB) : PMF (ΩA × ΩB) :=
  p.bind (fun a => q.map (fun b => (a,b)))

axiom pair_mass_pmf_event {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (p : PMF ΩA) (q : PMF ΩB) (H : ΩA → ΩB → Prop) :
    pairMass (weights p) (weights q) H =
      ((independentPair p q).toOuterMeasure {ab | H ab.1 ab.2}).toReal

end Lax342547.PairRecovery
end
