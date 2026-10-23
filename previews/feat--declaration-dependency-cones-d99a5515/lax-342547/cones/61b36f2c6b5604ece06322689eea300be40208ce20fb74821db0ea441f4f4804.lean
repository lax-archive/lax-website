-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
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

-- Lax342547.RawFrames
section
namespace Lax342547.RawFrames
end Lax342547.RawFrames

namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame
end

-- Lax342547.RawLaw
section
namespace Lax342547.RawLaw
end Lax342547.RawLaw
end

-- Lax342547.FrameSymmetry
section
namespace Lax342547.FrameSymmetry
end Lax342547.FrameSymmetry

namespace Lax342547.FrameSymmetry.Change
end Lax342547.FrameSymmetry.Change
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

open Lax342547.MomentSpace

open scoped ENNReal

variable {I J N : Type} [Fintype I] [Fintype J] [Fintype N]

abbrev GramFiber (A : Matrix N I Binary) (G : Matrix I J Binary) :=
  {B : Matrix N J Binary // A.transpose * B = G}

end Lax342547.GramColumns
end

-- Lax342547.ConditionalMinus
section
namespace Lax342547.ConditionalMinus

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.GramColumns

open scoped ENNReal

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

abbrev ColumnProduct (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :=
  GramFiber (Matrix.fromCols P X) (Matrix.fromRows E 0) × GramFiber P (0 : Matrix B H Binary)

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

open Lax342547.MomentSpace Lax342547.ConditionalMinus Lax342547.ProductImages

open scoped ENNReal

variable {Draw B H T N : Type} [Fintype Draw] [Fintype B] [Fintype H] [Fintype T] [Fintype N]

def images {E : Matrix B B Binary} {P : Draw → Matrix N B Binary} {X : Draw → Matrix N H Binary}
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (z : ∀ i, ColumnProduct E (P i) (X i)) : Matrix N T Binary :=
  jointMatrix (fun i => Matrix.fromCols (z i).1.val (z i).2.val) * C

end Lax342547.ProductMinusImages
end
