-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
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

-- Lax342547.LeafTrimming
section
namespace Lax342547.LeafTrimming
end Lax342547.LeafTrimming
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
end Lax342547.ExactPins

namespace Lax342547.ExactPins.Pin
end Lax342547.ExactPins.Pin
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

end Lax342547.MetadataPins
end

-- Lax342547.SplitTrimming
section
namespace Lax342547.SplitTrimming

open Lax342547.MomentSpace Lax342547.MetadataPins

open scoped ENNReal

axiom metadata_discard {Ω J Axis I N : Type}
    [Fintype J] [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (choice : Ω → J) (S : J → Axis → Submodule Binary (I → Binary)) (a n u : ℕ)
    (hchoices : Fintype.card J ≤ 2 ^ (a * n))
    (hu : ∀ j, ∑ b, Module.finrank Binary (S j b) ≤ u) :
    p.toOuterMeasure {o | p.toOuterMeasure {x | record A choice S x = record A choice S o} <
        (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N))} ≤
      (2 : ℝ≥0∞) ^ ((a * n : ℕ) - (Fintype.card N : ℝ))

end Lax342547.SplitTrimming
end
