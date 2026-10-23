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

open Lax342547.MomentSpace

variable (B H N : Type) [Fintype B] [Fintype H] [Fintype N]

structure Frame (E : Matrix B B Binary) where
  P : Matrix N B Binary
  Q : Matrix N B Binary
  X : Matrix N H Binary
  Y : Matrix N H Binary
  plus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => P.mulVec z.1 + X.mulVec z.2)
  minus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => Q.mulVec z.1 + Y.mulVec z.2)
  gram : P.transpose * Q = E
  plus_annihilator : X.transpose * Q = 0
  minus_annihilator : P.transpose * Y = 0

variable {B H N}

abbrev FrameData := Matrix N B Binary × Matrix N B Binary × Matrix N H Binary × Matrix N H Binary

def frameData {E : Matrix B B Binary} (F : Frame B H N E) : FrameData (B := B) (H := H) (N := N) :=
  (F.P, F.Q, F.X, F.Y)

theorem frameData_injective {E : Matrix B B Binary} :
    Function.Injective (frameData (E := E) (H := H) (N := N)) := by
  intro F G h
  cases F
  cases G
  simp only [frameData, Prod.mk.injEq] at h
  obtain ⟨hP, hQ, hX, hY⟩ := h
  cases hP
  cases hQ
  cases hX
  cases hY
  rfl

noncomputable instance {E : Matrix B B Binary} : Fintype (Frame B H N E) :=
  by classical exact Fintype.ofInjective frameData frameData_injective

variable {Comp : Type}

end Lax342547.RawFrames
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

noncomputable instance (A : Matrix N I Binary) (G : Matrix I J Binary) : Fintype (GramFiber A G) := by
  classical exact Subtype.fintype _

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

def Good {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (z : ColumnProduct E P X) : Prop :=
  Function.Injective (fun w : (B → Binary) × (H → Binary) =>
    z.1.val.mulVec w.1 + z.2.val.mulVec w.2)

abbrev Completion (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :=
  {z : ColumnProduct E P X // Good z}

abbrev Fiber (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :=
  {F : Frame B H N E // F.P = P ∧ F.X = X}

noncomputable instance (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :
    Fintype (Completion E P X) := by classical exact Subtype.fintype _

noncomputable instance (E : Matrix B B Binary) (P : Matrix N B Binary) (X : Matrix N H Binary) :
    Fintype (Fiber E P X) := by classical exact Subtype.fintype _

def columns {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (F : Fiber E P X) : Completion E P X :=
  ⟨(⟨F.val.Q, by
       simp only [← F.property.1, ← F.property.2, Matrix.transpose_fromCols,
         Matrix.fromRows_mul, F.val.gram, F.val.plus_annihilator]⟩,
    ⟨F.val.Y, by simpa only [← F.property.1] using F.val.minus_annihilator⟩), F.val.minus_injective⟩

axiom conditional_uniform {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec)
    [Nonempty (Fiber E P X)] [Nonempty (Completion E P X)] :
    (PMF.uniformOfFintype (Fiber E P X)).map columns = PMF.uniformOfFintype (Completion E P X)

end Lax342547.ConditionalMinus
end
