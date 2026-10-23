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

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw
end Lax342547.FiniteLinearLaw
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

end Lax342547.FrameSymmetry
end

-- Lax342547.AffineImages
section
namespace Lax342547.AffineImages
end Lax342547.AffineImages
end

-- Lax342547.GramColumns
section
namespace Lax342547.GramColumns
end Lax342547.GramColumns
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

axiom raw_plus_image_bound {Draw B H T N : Type}
    [Fintype Draw] [Fintype B] [Fintype H] [Fintype T] [Fintype N]
    [DecidableEq Draw] [DecidableEq B] [DecidableEq H] [DecidableEq T] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (hN : Fintype.card B + Fintype.card H + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (hC : Function.Injective C.mulVec)
    (y : Matrix N T Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).map
      (fun o => jointMatrix (fun i => (plus (o i)).val) * C) y ≤
      (2 : ℝ≥0∞) ^ Fintype.card Draw / 2 ^ (Fintype.card N * Fintype.card T)

end Lax342547.ProductImages
end
