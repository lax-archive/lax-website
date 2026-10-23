-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.SetTheory.Cardinal.Finite

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

end Pin

end Lax342547.ExactPins
end

-- Lax342547.MetadataPins
section
namespace Lax342547.MetadataPins

open Lax342547.MomentSpace Lax342547.ExactPins

def Images {Axis I : Type} (N : Type) (S : Axis → Submodule Binary (I → Binary)) :=
  ∀ a, S a →ₗ[Binary] (N → Binary)

def Key {J Axis I : Type} (N : Type) (S : J → Axis → Submodule Binary (I → Binary)) :=
  Σ j, Images N (S j)

def pin {J Axis I N : Type} {S : J → Axis → Submodule Binary (I → Binary)}
    (k : Key N S) : Pin Axis I N := ⟨S k.1, k.2⟩

end Lax342547.MetadataPins
end
