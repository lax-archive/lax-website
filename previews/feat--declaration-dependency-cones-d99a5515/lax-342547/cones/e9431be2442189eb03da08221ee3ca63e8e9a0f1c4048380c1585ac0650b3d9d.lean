-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
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

open Lax342547.PushforwardWalsh

noncomputable def cellMass {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if C ω then ρ ω else 0

end Lax342547.RetainedImages
end

-- Lax342547.RelativeEntropy
section
namespace Lax342547.RelativeEntropy
end Lax342547.RelativeEntropy
end

-- Lax342547.EntropyLines
section
namespace Lax342547.EntropyLines
end Lax342547.EntropyLines
end

-- Lax342547.EntropyProjection
section
namespace Lax342547.EntropyProjection
end Lax342547.EntropyProjection
end

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.RealCellLaws
section
namespace Lax342547.RealCellLaws
end Lax342547.RealCellLaws
end

-- Lax342547.PairRecovery
section
namespace Lax342547.PairRecovery
end Lax342547.PairRecovery
end

-- Lax342547.UnitLaws
section
namespace Lax342547.UnitLaws
end Lax342547.UnitLaws
end

-- Lax342547.ContainerLaws
section
namespace Lax342547.ContainerLaws
end Lax342547.ContainerLaws
end

-- Lax342547.FiniteSampling
section
namespace Lax342547.FiniteSampling
end Lax342547.FiniteSampling
end

-- Lax342547.SelectorInterpolation
section
namespace Lax342547.SelectorInterpolation

open Lax342547.MomentSpace

def monomial {b : ℕ} (S : Finset (Fin b)) : (Fin b → Binary) → Binary :=
  fun s => ∏ i ∈ S, s i

def selectorSpan (b degree : ℕ) : Submodule Binary ((Fin b → Binary) → Binary) :=
  Submodule.span Binary {f | ∃ S : Finset (Fin b), S.card ≤ degree ∧ f = monomial S}

end Lax342547.SelectorInterpolation
end

-- Lax342547.BooleanWeight
section
namespace Lax342547.BooleanWeight

open Lax342547.MomentSpace Lax342547.SelectorInterpolation

open scoped BigOperators

axiom uniform_error_exactification {b d : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b d)
    (herr : Lax342547.RetainedImages.cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => f x ≠ 0) < 1/(2 : ℝ)^d) : f = 0

end Lax342547.BooleanWeight
end
