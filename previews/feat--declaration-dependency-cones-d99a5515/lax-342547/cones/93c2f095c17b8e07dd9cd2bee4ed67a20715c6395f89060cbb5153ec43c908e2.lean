-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.SetTheory.Cardinal.Finite

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

end Lax342547.BoundedPeeling
end

-- Lax342547.LeafTrimming
section
namespace Lax342547.LeafTrimming
end Lax342547.LeafTrimming
end

-- Lax342547.MetadataPins
section
namespace Lax342547.MetadataPins

open Lax342547.MomentSpace Lax342547.ExactPins

def Images {Axis I : Type} (N : Type) (S : Axis → Submodule Binary (I → Binary)) :=
  ∀ a, S a →ₗ[Binary] (N → Binary)

def Key {J Axis I : Type} (N : Type) (S : J → Axis → Submodule Binary (I → Binary)) :=
  Σ j, Images N (S j)

def record {Ω J Axis I N : Type}
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (choice : Ω → J)
    (S : J → Axis → Submodule Binary (I → Binary)) (o : Ω) : Key N S :=
  ⟨choice o, fun a => (A o a).comp (S (choice o) a).subtype⟩

def pin {J Axis I N : Type} {S : J → Axis → Submodule Binary (I → Binary)}
    (k : Key N S) : Pin Axis I N := ⟨S k.1, k.2⟩

end Lax342547.MetadataPins
end

-- Lax342547.SplitTrimming
section
namespace Lax342547.SplitTrimming
end Lax342547.SplitTrimming
end

-- Lax342547.SecondPeeling
section
namespace Lax342547.SecondPeeling

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.MetadataPins

open Lax342547.LeafPartition Lax342547.BoundedPeeling

open scoped ENNReal

def startCost (D : ℝ) (K₁ u : ℕ) : ℝ := D + K₁ + u + 5

noncomputable def newBudget (D ζ : ℝ) (K₁ u : ℕ) : ℕ :=
  ⌈4 * (startCost D K₁ u + 1) / ζ⌉₊

noncomputable def finalBudget (D ζ : ℝ) (K₁ u : ℕ) : ℕ :=
  ⌈10 * (D + K₁ + u + 10) / ζ⌉₊

noncomputable def supportFinset {Ω : Type} [Fintype Ω] (p : PMF Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun o => o ∈ p.support)

def RepeeledPart {Ω J Axis I N : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Axis] [Fintype N]
    (q μ : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (choice : Ω → J) (U : J → Axis → Submodule Binary (I → Binary))
    (D ζ : ℝ) (K₁ u : ℕ) (k : Key N U) : Prop :=
  ∃ hkSupport : ∃ o ∈ {o | record A choice U o = k}, o ∈ q.support,
  let Q := q.filter {o | record A choice U o = k} hkSupport
  ∃ P : Pin Axis I N, ∃ L : Finset (Finset Ω × Pin Axis I N),
    P₀.Extends P ∧ (pin k).Extends P ∧ P.rank ≤ K₁ + u ∧
    Partition Q A P (supportFinset Q)
      ((2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)))
      ((2 : ℝ≥0∞) ^ (-((1 - ζ) * Fintype.card N))) L ∧
    q.toOuterMeasure (supportFinset Q \ L.biUnion Prod.fst) ≤
      (2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)) *
        q.toOuterMeasure {o | record A choice U o = k} ∧
    ∀ z ∈ L, z.2.rank ≤ finalBudget D ζ K₁ u ∧
      LawBound Q μ A z.2 z.1
        ((2 : ℝ≥0∞) ^ (-((1 - ζ) * Fintype.card N)))
        ((2 : ℝ≥0∞) ^ ((startCost D K₁ u + newBudget D ζ K₁ u + 1) * Fintype.card N))

axiom second_part {Ω J Axis I N : Type}
    [Fintype Ω] [DecidableEq Ω] [Fintype Axis] [Fintype I] [Fintype N]
    (p μ : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support)
    (choice : Ω → J) (U : J → Axis → Submodule Binary (I → Binary))
    (D ζ ε : ℝ) (K₁ u : ℕ)
    (hD : 0 ≤ D) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : ε ≤ ζ / 4)
    (hN : 0 < Fintype.card N) (hP : p.support ⊆ P₀.event A) (hPbudget : P₀.rank ≤ K₁)
    (hu : ∀ j, ∑ a, Module.finrank Binary (U j a) ≤ u)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)) ≤ p.toOuterMeasure S)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ ((D + K₁ + 1) * Fintype.card N) * μ o)
    (hreference : ∀ P : Pin Axis I N, μ.toOuterMeasure (P.event A) ≤
      (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * Fintype.card N)))
    (k : Key N U)
    (hk : (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N)) ≤
      (p.filter S hS).toOuterMeasure {o | record A choice U o = k}) :
    RepeeledPart (p.filter S hS) μ A P₀ choice U D ζ K₁ u k

end Lax342547.SecondPeeling
end
