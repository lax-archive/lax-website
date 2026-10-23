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
namespace Lax342547.ContainerRun

noncomputable def next {U : Type} (H : U → U → Prop) (I R : Finset U) (v : U) : Finset U := by
  classical
  exact if v ∈ I then R.filter (fun w => ¬ H v w) else R.erase v

noncomputable def run {U : Type} (active : Finset U → Prop) (pick : Finset U → U)
    (H : U → U → Prop) (I : Finset U) : ℕ → Finset U → Finset U × List U := by
  classical
  exact fun fuel R => match fuel with
  | 0 => (R,[])
  | n+1 => if active R then
      let v := pick R
      let result := run active pick H I n (next H I R v)
      (result.1,if v ∈ I then v::result.2 else result.2)
    else (R,[])

end Lax342547.ContainerRun
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

axiom entropy_fingerprint_length {U : Type} [Fintype U]
    (P : Set (U → ℝ)) (q : U → ℝ) (H : U → U → Prop) (ε B : ℝ)
    (law : Finset U → U → ℝ) (pick : Finset U → U) (I R : Finset U) (fuel L : ℕ)
    (hprob : ∀ ρ ∈ P, Probability ρ) (hc : Convex ℝ P)
    (hb : ∀ ρ ∈ P, 0 ≤ entropy ρ q ∧ entropy ρ q ≤ B)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hspec : ∀ T, (residual P T).Nonempty →
      law T ∈ residual P T ∧ (∀ σ ∈ residual P T, entropy (law T) q ≤ entropy σ q) ∧
      pick T ∈ T ∧ ε ≤ neighborMass (law T) H (pick T) ∧ (∃ w ∈ T, H (pick T) w))
    (hL : B/(-Real.log (1-ε))+1 ≤ L) (hactive : (residual P R).Nonempty) :
    (run (fun T => (residual P T).Nonempty) pick H I fuel R).2.length ≤ L

end Lax342547.EntropyContainers
end
