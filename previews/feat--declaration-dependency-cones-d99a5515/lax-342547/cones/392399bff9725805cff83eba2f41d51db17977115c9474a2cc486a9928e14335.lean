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

axiom exists_leaf {Ω Axis I N : Type}
    [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Set Ω) (hR : R ⊆ P₀.event A)
    (δ α : ℝ≥0∞) (hα₀ : α ≠ 0) (hαtop : α ≠ ⊤) (hmass : δ < p.toOuterMeasure R) :
    ∃ P : Pin Axis I N, P₀.Extends P ∧
      δ * α ^ (P.rank - P₀.rank) < p.toOuterMeasure (R ∩ P.event A) ∧
      Good p A P (R ∩ P.event A) α

end Lax342547.LeafExtraction
end
