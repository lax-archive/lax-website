-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
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

end Lax342547.BoundedPeeling
end

-- Lax342547.RawFrames
section
namespace Lax342547.RawFrames

open Lax342547.MomentSpace

variable (B H N : Type) [Fintype B] [Fintype H] [Fintype N]

structure Frame (E : Matrix B B Binary) where
  P : Matrix N B Binary
  Q : Matrix N B Binary
  X : Matrix N H Binary
  Y : Matrix N H Binary
  plus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => P.mulVec z.1 + X.mulVec z.2)
  minus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => Q.mulVec z.1 + Y.mulVec z.2)
  gram : P.transpose * Q = E
  plus_annihilator : X.transpose * Q = 0
  minus_annihilator : P.transpose * Y = 0

variable {B H N}

abbrev FrameData := Matrix N B Binary × Matrix N B Binary × Matrix N H Binary × Matrix N H Binary

def frameData {E : Matrix B B Binary} (F : Frame B H N E) : FrameData (B := B) (H := H) (N := N) :=
  (F.P, F.Q, F.X, F.Y)

theorem frameData_injective {E : Matrix B B Binary} :
    Function.Injective (frameData (E := E) (H := H) (N := N)) := by
  intro F G h
  cases F
  cases G
  simp only [frameData, Prod.mk.injEq] at h
  obtain ⟨hP, hQ, hX, hY⟩ := h
  cases hP
  cases hQ
  cases hX
  cases hY
  rfl

noncomputable instance {E : Matrix B B Binary} : Fintype (Frame B H N E) :=
  by classical exact Fintype.ofInjective frameData frameData_injective

variable {Comp : Type}

end Lax342547.RawFrames
end

-- Lax342547.RawLaw
section
namespace Lax342547.RawLaw
end Lax342547.RawLaw
end

-- Lax342547.FrameSymmetry
section
namespace Lax342547.FrameSymmetry.Change
end Lax342547.FrameSymmetry.Change

namespace Lax342547.FrameSymmetry

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N] [DecidableEq N]

abbrev Injection (I N : Type) [Fintype I] :=
  {A : Matrix N I Binary // Function.Injective A.mulVec}

def plus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.P F.X, by
    intro x y h
    have h' := F.plus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

def minus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.Q F.Y, by
    intro x y h
    have h' := F.minus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

end Lax342547.FrameSymmetry
end

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw
end Lax342547.FiniteLinearLaw
end

-- Lax342547.AffineImages
section
namespace Lax342547.AffineImages
end Lax342547.AffineImages
end

-- Lax342547.GramColumns
section
namespace Lax342547.GramColumns
end Lax342547.GramColumns
end

-- Lax342547.ConditionalMinus
section
namespace Lax342547.ConditionalMinus
end Lax342547.ConditionalMinus
end

-- Lax342547.GramNormalization
section
namespace Lax342547.GramNormalization
end Lax342547.GramNormalization
end

-- Lax342547.InjectiveFrames
section
namespace Lax342547.InjectiveFrames
end Lax342547.InjectiveFrames
end

-- Lax342547.ProductImages
section
namespace Lax342547.ProductImages

open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.RawFrames

open scoped ENNReal

def jointMatrix {Draw I N : Type} (A : Draw → Matrix N I Binary) : Matrix N (Draw × I) Binary :=
  fun n j => A j.1 n j.2

end Lax342547.ProductImages
end

-- Lax342547.ProductMinusImages
section
namespace Lax342547.ProductMinusImages
end Lax342547.ProductMinusImages
end

-- Lax342547.ReferenceImages
section
namespace Lax342547.ReferenceImages
end Lax342547.ReferenceImages
end

-- Lax342547.ImageScale
section
namespace Lax342547.ImageScale
end Lax342547.ImageScale
end

-- Lax342547.ReferencePins
section
namespace Lax342547.ReferencePins

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

open Lax342547.ProductImages Lax342547.ExactPins

open scoped ENNReal

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]

def observationMatrix {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : Matrix N (Fin 2 × (B ⊕ H)) Binary :=
  if a.2 then jointMatrix (fun i => (plus (o i a.1)).val)
  else jointMatrix (fun i => (minus (o i a.1)).val)

def observation {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary) :=
  (observationMatrix o a).mulVecLin

end Lax342547.ReferencePins
end

-- Lax342547.RawPeeling
section
namespace Lax342547.RawPeeling

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins

open Lax342547.ReferencePins Lax342547.LeafPartition Lax342547.BoundedPeeling

open scoped ENNReal

axiom raw_peeling {Comp B H N : Type}
    [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)] [DecidableEq (Frame B H N E)]
    (σ : PMF (Fin 2 → Comp → Frame B H N E))
    (P₀ : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (R : Finset (Fin 2 → Comp → Frame B H N E))
    (hR : (R : Set (Fin 2 → Comp → Frame B H N E)) ⊆ P₀.event observation)
    (D ζ ε : ℝ) (K : ℕ)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : 0 < ε) (hεζ : ε ≤ ζ / 4)
    (hK : 4 * (D + 1) / ζ ≤ K)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ ε * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ ε * Fintype.card N)
    (hσ : ∀ o, σ o ≤ (2 : ℝ≥0∞) ^ (D * Fintype.card N) * PMF.uniformOfFintype _ o) :
    ∃ L : Finset (Finset (Fin 2 → Comp → Frame B H N E) × Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N),
      Partition σ observation P₀ R ((2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)))
        ((2 : ℝ≥0∞) ^ (-((1 - ζ) * Fintype.card N))) L ∧
      ∀ z ∈ L, z.2.rank ≤ P₀.rank + K ∧
        LawBound σ (PMF.uniformOfFintype _) observation z.2 z.1
          ((2 : ℝ≥0∞) ^ (-((1 - ζ) * Fintype.card N)))
          ((2 : ℝ≥0∞) ^ ((D + K + 1) * Fintype.card N))

end Lax342547.RawPeeling
end
