-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.Distributions.Uniform

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

-- Lax342547.FrameTuples
section
namespace Lax342547.FrameTuples

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

abbrev Orbit {I J : Type} (N : Type) [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) :=
  {z : Matrix N I Binary × Matrix N J Binary //
    Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec ∧ z.1.transpose * z.2 = G}

noncomputable instance {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) : Fintype (Orbit N G) := by classical exact Subtype.fintype _

variable {B H I J N : Type} [Fintype B] [Fintype H] [Fintype I] [Fintype J] [Fintype N]

def primalTuple {E : Matrix B B Binary} (C : Matrix B I Binary) (D : Matrix B J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    (F : Frame B H N E) : Orbit N (C.transpose * E * D) :=
  ⟨(F.P * C, F.Q * D), by
    refine ⟨?_, ?_, ?_⟩
    · intro x y h
      apply hC
      have he := F.plus_injective (a₁ := (C.mulVec x, 0)) (a₂ := (C.mulVec y, 0))
        (by simpa only [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec] using h)
      exact congrArg Prod.fst he
    · intro x y h
      apply hD
      have he := F.minus_injective (a₁ := (D.mulVec x, 0)) (a₂ := (D.mulVec y, 0))
        (by simpa only [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec] using h)
      exact congrArg Prod.fst he
    · calc
        _ = C.transpose * (F.P.transpose * F.Q) * D := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = _ := by rw [F.gram]⟩

axiom primal_uniform [DecidableEq N] {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (C : Matrix B I Binary) (D : Matrix B J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose * E * D))] :
    (PMF.uniformOfFintype (Frame B H N E)).map (primalTuple C D hC hD) =
      PMF.uniformOfFintype (Orbit N (C.transpose * E * D))

end Lax342547.FrameTuples
end
