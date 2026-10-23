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
end Lax342547.ExactPins

namespace Lax342547.ExactPins.Pin
end Lax342547.ExactPins.Pin
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

open Lax342547.MomentSpace

axiom appended_quotient_injective {U V W : Type}
    [AddCommGroup U] [Module Binary U] [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W]
    (P : Submodule Binary W) (keys : U →ₗ[Binary] W) (fresh : V →ₗ[Binary] W)
    (hkeys : Function.Injective (P.mkQ.comp keys))
    (hfresh : Function.Injective ((P ⊔ LinearMap.range keys).mkQ.comp fresh)) :
    Function.Injective (P.mkQ.comp (keys.coprod fresh))

end Lax342547.JointDirections
end
