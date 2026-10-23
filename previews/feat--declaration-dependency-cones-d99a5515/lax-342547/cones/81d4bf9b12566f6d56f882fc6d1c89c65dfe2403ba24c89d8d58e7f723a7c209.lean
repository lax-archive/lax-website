-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas

-- Lax342547.ContainerRun
section
namespace Lax342547
end Lax342547

namespace Lax342547.ContainerRun
end Lax342547.ContainerRun

namespace Lax342547.ContainerRun.run
end Lax342547.ContainerRun.run
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

open Lax342547.PushforwardWalsh

noncomputable def cellMass {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if C ω then ρ ω else 0

end Lax342547.RetainedImages
end

-- Lax342547.RelativeEntropy
section
namespace Lax342547.RelativeEntropy

open scoped BigOperators

noncomputable def entropy {Ω : Type} [Fintype Ω] (ρ q : Ω → ℝ) : ℝ :=
  ∑ x, (ρ x * Real.log (ρ x) - ρ x * Real.log (q x))

def Probability {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ ρ x) ∧ ∑ x, ρ x = 1

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

open Lax342547.RelativeEntropy Lax342547.RetainedImages

open scoped BigOperators

noncomputable def residual {U : Type} [Fintype U] (P : Set (U → ℝ)) (R : Finset U) : Set (U → ℝ) :=
  {ρ | ρ ∈ P ∧ ∀ x, x ∉ R → ρ x = 0}

noncomputable def neighborMass {U : Type} [Fintype U] (ρ : U → ℝ) (H : U → U → Prop) (v : U) : ℝ :=
  cellMass ρ (H v)

noncomputable def conflictMass {U : Type} [Fintype U] (ρ : U → ℝ) (H : U → U → Prop) : ℝ :=
  ∑ v, ρ v * neighborMass ρ H v

end Lax342547.ContainerLaws
end

-- Lax342547.EntropySelectors
section
namespace Lax342547.EntropySelectors
end Lax342547.EntropySelectors
end

-- Lax342547.FingerprintCounts
section
namespace Lax342547
end Lax342547

namespace Lax342547.FingerprintCounts
end Lax342547.FingerprintCounts
end

-- Lax342547.EntropyContainers
section
namespace Lax342547.EntropyContainers

open Lax342547.RelativeEntropy Lax342547.ContainerLaws Lax342547.ContainerRun

open scoped BigOperators

axiom entropy_container_family {U : Type} [Fintype U] [Nonempty U]
    (P : Set (U → ℝ)) (q : U → ℝ) (H : U → U → Prop) (ε B : ℝ) (L : ℕ)
    (hcompact : IsCompact P) (hconvex : Convex ℝ P) (hprob : ∀ ρ ∈ P, Probability ρ)
    (hbudget : ∀ ρ ∈ P, 0 ≤ entropy ρ q ∧ entropy ρ q ≤ B)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hL : B/(-Real.log (1-ε))+1 ≤ L)
    (hsuper : ∀ ρ ∈ P, ε ≤ conflictMass ρ H) :
    ∃ C : Finset (Finset U),
      C.card ≤ (Fintype.card U+1)^L ∧
      (∀ R ∈ C, ¬ (residual P R).Nonempty) ∧
      (∀ I : Finset U, (∀ x ∈ I, ∀ y ∈ I, ¬ H x y) → ∃ R ∈ C, I ⊆ R)

end Lax342547.EntropyContainers
end
