-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
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

open Lax342547.MomentSpace Lax342547.ExactPins

open scoped ENNReal

axiom leaf_key_fresh_image_cap {Ω Axis I N : Type} {U V : Axis → Type}
    [Fintype Axis] [Fintype I]
    [∀ a, AddCommGroup (U a)] [∀ a, Module Binary (U a)] [∀ a, FiniteDimensional Binary (U a)]
    [∀ a, AddCommGroup (V a)] [∀ a, Module Binary (V a)] [∀ a, FiniteDimensional Binary (V a)]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (keys : ∀ a, U a →ₗ[Binary] (I → Binary))
    (fresh : ∀ a, V a →ₗ[Binary] (I → Binary))
    (hkeys : ∀ a, Function.Injective ((P.space a).mkQ.comp (keys a)))
    (hfresh : ∀ a, Function.Injective (((P.space a) ⊔ LinearMap.range (keys a)).mkQ.comp (fresh a)))
    (yk : ∀ a, U a →ₗ[Binary] (N → Binary)) (yf : ∀ a, V a →ₗ[Binary] (N → Binary))
    (α : ℝ≥0∞)
    (hcap : ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      p.toOuterMeasure (Q.event A) ≤ α ^ (P.relativeRank Q))
    (hr : 1 ≤ (∑ a, Module.finrank Binary (U a)) + ∑ a, Module.finrank Binary (V a)) :
    p.toOuterMeasure {ω | ∀ a, (A ω a).comp (keys a) = yk a ∧ (A ω a).comp (fresh a) = yf a} ≤
      α ^ ((∑ a, Module.finrank Binary (U a)) + ∑ a, Module.finrank Binary (V a))

end Lax342547.JointKeyCap
end
