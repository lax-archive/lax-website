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

noncomputable def relativeRank [Fintype Axis] (P Q : Pin Axis I N) : ℕ :=
  ∑ a, Module.finrank Binary ((Q.space a).map (P.space a).mkQ)

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

open Lax342547.MomentSpace Lax342547.ExactPins

open scoped ENNReal

noncomputable def imagePin {Ω Axis I N : Type}
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (S : Axis → Submodule Binary (I → Binary)) (o : Ω) : Pin Axis I N :=
  ⟨S, fun a => (A o a).comp (S a).subtype⟩

axiom image_pin_relative_rank {Ω Axis I N : Type} {R : Axis → Type}
    [Fintype Axis] [Fintype I]
    [∀ a, AddCommGroup (R a)] [∀ a, Module Binary (R a)] [∀ a, FiniteDimensional Binary (R a)]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (f : ∀ a, R a →ₗ[Binary] (I → Binary))
    (hf : ∀ a, Function.Injective ((P.space a).mkQ.comp (f a))) (o : Ω) :
    P.relativeRank (imagePin A (fun a => LinearMap.range (f a)) o) =
      ∑ a, Module.finrank Binary (R a)

end Lax342547.LeafImages
end
