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
namespace Lax342547.FrameSymmetry.Change
end Lax342547.FrameSymmetry.Change

namespace Lax342547.FrameSymmetry

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N] [DecidableEq N]

abbrev Injection (I N : Type) [Fintype I] :=
  {A : Matrix N I Binary // Function.Injective A.mulVec}

def plus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.P F.X, by
    intro x y h
    have h' := F.plus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

def minus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.Q F.Y, by
    intro x y h
    have h' := F.minus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

end Lax342547.FrameSymmetry
end

-- Lax342547.FrameTuples
section
namespace Lax342547.FrameTuples

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

abbrev Orbit {I J : Type} (N : Type) [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) :=
  {z : Matrix N I Binary × Matrix N J Binary //
    Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec ∧ z.1.transpose * z.2 = G}

variable {B H I J N : Type} [Fintype B] [Fintype H] [Fintype I] [Fintype J] [Fintype N]

def fullGram (E : Matrix B B Binary) (G : Matrix H H Binary) : Matrix (B ⊕ H) (B ⊕ H) Binary :=
  Matrix.fromBlocks E 0 0 G

abbrev ChannelFiber (E : Matrix B B Binary) (G : Matrix H H Binary) :=
  {F : Frame B H N E // F.X.transpose * F.Y = G}

theorem combined_gram {E : Matrix B B Binary} (F : Frame B H N E) :
    (plus F).val.transpose * (minus F).val = fullGram E (F.X.transpose * F.Y) := by
  simp only [plus, minus, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
    F.gram, F.plus_annihilator, F.minus_annihilator, fullGram]

def fullTuple {E : Matrix B B Binary} {G : Matrix H H Binary}
    (C : Matrix (B ⊕ H) I Binary) (D : Matrix (B ⊕ H) J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    (F : ChannelFiber (N := N) E G) : Orbit N (C.transpose * fullGram E G * D) :=
  ⟨((plus F.val).val * C, (minus F.val).val * D), by
    refine ⟨?_, ?_, ?_⟩
    · intro x y h
      apply hC
      apply (plus F.val).property
      simpa only [Matrix.mulVec_mulVec] using h
    · intro x y h
      apply hD
      apply (minus F.val).property
      simpa only [Matrix.mulVec_mulVec] using h
    · calc
        _ = C.transpose * ((plus F.val).val.transpose * (minus F.val).val) * D := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = _ := by rw [combined_gram, F.property]⟩

end Lax342547.FrameTuples
end
