-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Isomorphisms
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
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.ExactPins
section
namespace Lax342547.ExactPins

open Lax342547.MomentSpace

def Pin (Axis I N : Type) :=
  Σ S : Axis → Submodule Binary (I → Binary), ∀ a, S a →ₗ[Binary] (N → Binary)

namespace Pin

variable {Axis I N : Type}

def space (P : Pin Axis I N) (a : Axis) : Submodule Binary (I → Binary) := P.1 a

def value (P : Pin Axis I N) (a : Axis) : P.space a →ₗ[Binary] (N → Binary) := P.2 a

noncomputable def relativeRank [Fintype Axis] (P Q : Pin Axis I N) : ℕ :=
  ∑ a, Module.finrank Binary ((Q.space a).map (P.space a).mkQ)

def event {Ω : Type} (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) : Set Ω :=
  {o | ∀ a (v : P.space a), A o a v.val = P.value a v}

end Pin

end Lax342547.ExactPins
end

-- Lax342547.LeafExtraction
section
namespace Lax342547.LeafExtraction
end Lax342547.LeafExtraction
end

-- Lax342547.LeafPartition
section
namespace Lax342547.LeafPartition
end Lax342547.LeafPartition
end

-- Lax342547.PeelingBudget
section
namespace Lax342547
end Lax342547

namespace Lax342547.PeelingBudget
end Lax342547.PeelingBudget
end

-- Lax342547.BoundedPeeling
section
namespace Lax342547.BoundedPeeling

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.LeafPartition

open scoped ENNReal

def LawBound {Ω Axis I N : Type} [Fintype Axis] (p μ : PMF Ω)
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (S : Set Ω) (α c : ℝ≥0∞) : Prop :=
  ∃ hS : ∃ o ∈ S, o ∈ p.support,
    (∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      (p.filter S hS).toOuterMeasure (Q.event A) ≤ α ^ (P.relativeRank Q)) ∧
    (∀ o, (p.filter S hS) o ≤ c * μ o) ∧
    ∀ o, p.toOuterMeasure S * (p.filter S hS) o = S.indicator p o

end Lax342547.BoundedPeeling
end

-- Lax342547.LeafTrimming
section
namespace Lax342547.LeafTrimming

open scoped ENNReal

noncomputable def discardedMass {J : Type} [Fintype J]
    (w q : J → ℝ≥0∞) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, if q j < δ then w j * q j else 0

end Lax342547.LeafTrimming
end

-- Lax342547.RestrictedLeaves
section
namespace Lax342547.RestrictedLeaves

open Lax342547.MomentSpace Lax342547.ExactPins

open Lax342547.LeafTrimming Lax342547.BoundedPeeling

open scoped ENNReal

axiom restricted_family {Ω J Axis I N : Type}
    [Fintype Ω] [Fintype J] [Fintype Axis]
    (p : J → PMF Ω) (μ : PMF Ω)
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : J → Pin Axis I N) (S : J → Set Ω) (w : J → ℝ≥0∞)
    (C ζ η : ℝ) (n : ℕ) (hζ : 0 ≤ ζ) (hw : ∑ j, w j ≤ 1)
    (hq : (2 : ℝ≥0∞) ^ (-(η * n)) ≤ ∑ j, w j * (p j).toOuterMeasure (S j))
    (hcap : ∀ j (Q : Pin Axis I N), 1 ≤ (P j).relativeRank Q →
      (p j).toOuterMeasure (Q.event A) ≤
        ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n))) ^ (P j).relativeRank Q)
    (hdensity : ∀ j o, p j o ≤ (2 : ℝ≥0∞) ^ (C * n) * μ o) :
    discardedMass w (fun j => (p j).toOuterMeasure (S j)) ((2 : ℝ≥0∞) ^ (-(ζ * n))) /
        (∑ j, w j * (p j).toOuterMeasure (S j)) ≤ (2 : ℝ≥0∞) ^ (-((ζ - η) * n)) ∧
    ∀ j, (2 : ℝ≥0∞) ^ (-(ζ * n)) ≤ (p j).toOuterMeasure (S j) →
      LawBound (p j) μ A (P j) (S j)
        ((2 : ℝ≥0∞) ^ (-((1 - 2 * ζ) * n))) ((2 : ℝ≥0∞) ^ ((C + ζ) * n))

end Lax342547.RestrictedLeaves
end
