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

def Extends (P Q : Pin Axis I N) : Prop :=
  ∃ h : ∀ a, P.space a ≤ Q.space a,
    ∀ a (v : P.space a), Q.value a ⟨v.val, h a v.property⟩ = P.value a v

noncomputable def rank [Fintype Axis] (P : Pin Axis I N) : ℕ :=
  ∑ a, Module.finrank Binary (P.space a)

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

open Lax342547.MomentSpace Lax342547.ExactPins

open scoped ENNReal

def Good {Ω Axis I N : Type} [Fintype Axis] (p : PMF Ω)
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (S : Set Ω) (α : ℝ≥0∞) : Prop :=
  ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
    p.toOuterMeasure (S ∩ Q.event A) ≤ α ^ (P.relativeRank Q) * p.toOuterMeasure S

end Lax342547.LeafExtraction
end

-- Lax342547.LeafPartition
section
namespace Lax342547.LeafPartition

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.LeafExtraction

open scoped ENNReal

def Partition {Ω Axis I N : Type} [DecidableEq Ω] [Fintype Axis]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Finset Ω) (δ α : ℝ≥0∞)
    (L : Finset (Finset Ω × Pin Axis I N)) : Prop :=
  (∀ z ∈ L, z.1 ⊆ R ∧ P₀.Extends z.2 ∧ (z.1 : Set Ω) ⊆ z.2.event A ∧
    δ * α ^ (z.2.rank - P₀.rank) < p.toOuterMeasure z.1 ∧ Good p A z.2 z.1 α) ∧
  (∀ z ∈ L, ∀ w ∈ L, z ≠ w → Disjoint z.1 w.1) ∧
  p.toOuterMeasure (R \ L.biUnion Prod.fst : Finset Ω) ≤ δ

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

axiom bounded_partition {Ω Axis I N : Type}
    [Fintype Ω] [DecidableEq Ω] [Fintype Axis] [Fintype I] [Fintype N]
    (p μ : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Finset Ω) (hR : (R : Set Ω) ⊆ P₀.event A)
    (D ζ ε : ℝ) (n K : ℕ) (hn : 0 < n)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : ε ≤ ζ / 4) (hK : 4 * (D + 1) / ζ ≤ K)
    (hdensity : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ (D * n) * μ o)
    (hreference : ∀ P : Pin Axis I N,
      μ.toOuterMeasure (P.event A) ≤ (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * n))) :
    ∃ L : Finset (Finset Ω × Pin Axis I N),
      Partition p A P₀ R ((2 : ℝ≥0∞) ^ (-(ζ * n))) ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n))) L ∧
      ∀ z ∈ L, z.2.rank - P₀.rank ≤ K ∧
        LawBound p μ A z.2 z.1 ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n)))
          ((2 : ℝ≥0∞) ^ ((D + K + 1) * n))

end Lax342547.BoundedPeeling
end
