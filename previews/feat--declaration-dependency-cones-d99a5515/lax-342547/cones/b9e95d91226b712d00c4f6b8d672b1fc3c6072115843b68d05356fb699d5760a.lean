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
end Lax342547.PushforwardWalsh
end

-- Lax342547.RetainedImages
section
namespace Lax342547.RetainedImages
end Lax342547.RetainedImages
end

-- Lax342547.RealCellLaws
section
namespace Lax342547.RealCellLaws
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

end Lax342547.LeafCellImages
end
