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

noncomputable def rank [Fintype Axis] (P : Pin Axis I N) : ℕ :=
  ∑ a, Module.finrank Binary (P.space a)

noncomputable def relativeRank [Fintype Axis] (P Q : Pin Axis I N) : ℕ :=
  ∑ a, Module.finrank Binary ((Q.space a).map (P.space a).mkQ)

def joinAt {Ω : Type} (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P Q : Pin Axis I N) (o : Ω) : Pin Axis I N :=
  ⟨fun a => P.space a ⊔ Q.space a,
    fun a => (A o a).comp (P.space a ⊔ Q.space a).subtype⟩

end Pin

axiom rank_refinement {Ω Axis I N : Type} [Fintype Axis] [Fintype I]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (P Q : Pin Axis I N) (o : Ω) :
    (P.joinAt A Q o).rank = P.rank + P.relativeRank Q

end Lax342547.ExactPins
end
