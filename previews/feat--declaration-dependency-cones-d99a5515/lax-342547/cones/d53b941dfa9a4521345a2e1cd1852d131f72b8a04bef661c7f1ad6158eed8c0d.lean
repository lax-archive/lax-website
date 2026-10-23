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

omit [Fintype N] in
theorem combined_injective_iff (P : Matrix N B Binary) (X : Matrix N H Binary) :
    Function.Injective (Matrix.fromCols P X).mulVec ↔
      Function.Injective (fun z : (B → Binary) × (H → Binary) => P.mulVec z.1 + X.mulVec z.2) := by
  constructor
  · intro h z w he
    have h' := h (a₁ := Sum.elim z.1 z.2) (a₂ := Sum.elim w.1 w.2)
      (by simpa only [Matrix.fromCols_mulVec_sumElim] using he)
    exact Prod.ext (funext (fun b => congrFun h' (Sum.inl b)))
      (funext (fun j => congrFun h' (Sum.inr j)))
  · intro h z w he
    have h' := h (a₁ := (z ∘ Sum.inl, z ∘ Sum.inr)) (a₂ := (w ∘ Sum.inl, w ∘ Sum.inr))
      (by simpa only [Matrix.fromCols_mulVec] using he)
    funext j
    cases j with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr j => exact congrFun (congrArg Prod.snd h') j

def columns {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (F : Fiber E P X) : Completion E P X :=
  ⟨(⟨F.val.Q, by
       simp only [← F.property.1, ← F.property.2, Matrix.transpose_fromCols,
         Matrix.fromRows_mul, F.val.gram, F.val.plus_annihilator]⟩,
    ⟨F.val.Y, by simpa only [← F.property.1] using F.val.minus_annihilator⟩), F.val.minus_injective⟩

def assemble {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec) (z : Completion E P X) : Fiber E P X :=
  ⟨{ P := P, X := X, Q := z.val.1.val, Y := z.val.2.val,
      plus_injective := (combined_injective_iff P X).mp hPX,
      minus_injective := z.property,
      gram := (Matrix.fromRows_inj (by
        simpa only [Matrix.transpose_fromCols, Matrix.fromRows_mul] using z.val.1.property)).1,
      plus_annihilator := (Matrix.fromRows_inj (by
        simpa only [Matrix.transpose_fromCols, Matrix.fromRows_mul] using z.val.1.property)).2,
      minus_annihilator := z.val.2.property }, rfl, rfl⟩

def completionEquiv {E : Matrix B B Binary} {P : Matrix N B Binary} {X : Matrix N H Binary}
    (hPX : Function.Injective (Matrix.fromCols P X).mulVec) : Fiber E P X ≃ Completion E P X where
  toFun := columns
  invFun := assemble hPX
  left_inv F := by
    apply Subtype.ext
    apply frameData_injective
    exact Prod.ext F.property.1.symm (Prod.ext rfl (Prod.ext F.property.2.symm rfl))
  right_inv z := by cases z; rfl

end Lax342547.ConditionalMinus
end
