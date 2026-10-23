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
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Constructions

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

-- Lax342547.LeafImages
section
namespace Lax342547.LeafImages
end Lax342547.LeafImages
end

-- Lax342547.JointDirections
section
namespace Lax342547.JointDirections
end Lax342547.JointDirections
end

-- Lax342547.JointKeyCap
section
namespace Lax342547.JointKeyCap
end Lax342547.JointKeyCap
end

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh
end Lax342547.Walsh
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def push {Ω X : Type} [Fintype Ω] (ρ : Ω → ℝ) (image : Ω → X) (x : X) : ℝ := by
  classical
  exact ∑ ω, if image ω = x then ρ ω else 0

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

-- Lax342547.RealCellLaws
section
namespace Lax342547.RealCellLaws

open Lax342547.RetainedImages Lax342547.PushforwardWalsh

open scoped ENNReal

noncomputable def weights {Ω : Type} (p : PMF Ω) : Ω → ℝ := fun ω => (p ω).toReal

noncomputable def subtypeWeights {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) :
    {ω // C ω} → ℝ := fun ω => ρ ω.val / cellMass ρ C

end Lax342547.RealCellLaws
end

-- Lax342547.LeafCellImages
section
namespace Lax342547.LeafCellImages

open Lax342547.MomentSpace Lax342547.ExactPins

open Lax342547.RealCellLaws Lax342547.RetainedImages Lax342547.PushforwardWalsh

open scoped ENNReal

noncomputable def freshImage {Ω Axis I N : Type} {V : Axis → Type}
    [∀ a, AddCommGroup (V a)] [∀ a, Module Binary (V a)]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (fresh : ∀ a, V a →ₗ[Binary] (I → Binary))
    (ω : Ω) : ∀ a, V a →ₗ[Binary] (N → Binary) := fun a => (A ω a).comp (fresh a)

axiom original_leaf_cell_image_cap {Ω Axis I N : Type} {U V : Axis → Type}
    [Fintype Ω] [Fintype Axis] [Fintype I] [Fintype N]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    [∀ a, AddCommGroup (V a)] [∀ a, Module Binary (V a)] [∀ a, FiniteDimensional Binary (V a)]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary))
    (fresh : ∀ a, V a →ₗ[Binary] (I → Binary))
    (hkeys : ∀ a, Function.Injective ((P.space a).mkQ.comp (keys a)))
    (hfresh : ∀ a, Function.Injective (((P.space a) ⊔ LinearMap.range (keys a)).mkQ.comp (fresh a)))
    (yk : ∀ a, U a →ₗ[Binary] (N → Binary)) (C : Ω → Prop)
    (hCkey : ∀ ω, C ω → ∀ a, (A ω a).comp (keys a) = yk a)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1 / 1000)
    (hk : 2 * ζ * (∑ a, Module.finrank Binary (U a)) ≤ (1 / 500 : ℝ))
    (ht : 1 ≤ ∑ a, Module.finrank Binary (V a))
    (hC : (2 : ℝ)^(-(((∑ a, Module.finrank Binary (U a) : ℕ) : ℝ) + 1 / 100) * Fintype.card N) ≤
      (p.toOuterMeasure {ω | C ω}).toReal)
    (hcap : ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event A) ≤
        ((2 : ℝ≥0∞)^(-(1 - 2 * ζ) * Fintype.card N)) ^ (P.relativeRank Q))
    (y : ∀ a, V a →ₗ[Binary] (N → Binary)) : by
      classical
      exact push (subtypeWeights (weights p) C) (fun ω => freshImage A fresh ω.val) y ≤
        (2 : ℝ)^(-(95/100 : ℝ)*(∑ a, Module.finrank Binary (V a))*Fintype.card N)

end Lax342547.LeafCellImages
end
