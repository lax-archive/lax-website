-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
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

-- Lax342547.ExactPins
section
namespace Lax342547.ExactPins

open Lax342547.MomentSpace

def Pin (Axis I N : Type) :=
  Σ S : Axis → Submodule Binary (I → Binary), ∀ a, S a →ₗ[Binary] (N → Binary)

namespace Pin

variable {Axis I N : Type}

def space (P : Pin Axis I N) (a : Axis) : Submodule Binary (I → Binary) := P.1 a

end Pin

end Lax342547.ExactPins
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
end Lax342547.GramColumns
end

-- Lax342547.ConditionalMinus
section
namespace Lax342547.ConditionalMinus
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
end Lax342547.ProductImages
end

-- Lax342547.ProductMinusImages
section
namespace Lax342547.ProductMinusImages
end Lax342547.ProductMinusImages
end

-- Lax342547.ReferenceImages
section
namespace Lax342547.ReferenceImages
end Lax342547.ReferenceImages
end

-- Lax342547.ImageScale
section
namespace Lax342547.ImageScale
end Lax342547.ImageScale
end

-- Lax342547.ReferencePins
section
namespace Lax342547.ReferencePins
end Lax342547.ReferencePins
end

-- Lax342547.ProjectedPins
section
namespace Lax342547.ProjectedPins

open Lax342547.MomentSpace Lax342547.ExactPins

def primalProjection {B H : Type} (i : Fin 2) :
    ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (B → Binary) where
  toFun v b := v (i, Sum.inl b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projected {Comp B H N : Type} (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (i : Fin 2) (a : Comp × Bool) : Submodule Binary (B → Binary) :=
  (P.space a).map (primalProjection i)

end Lax342547.ProjectedPins
end

-- Lax342547.TableSpaces
section
namespace Lax342547.TableSpaces

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins

def primalEmbedding {B H : Type} (i : Fin 2) :
    (B → Binary) →ₗ[Binary] ((Fin 2 × (B ⊕ H)) → Binary) where
  toFun v x := if x.1 = i then Sum.elim v (fun _ => 0) x.2 else 0
  map_add' v w := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]
  map_smul' c v := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]

def channelEmbedding {B H : Type} (i : Fin 2) :
    (H → Binary) →ₗ[Binary] ((Fin 2 × (B ⊕ H)) → Binary) where
  toFun v x := if x.1 = i then Sum.elim (fun _ => 0) v x.2 else 0
  map_add' v w := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]
  map_smul' c v := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]

def tableSpace {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary) where
  carrier := {v | ∀ i, primalProjection i v ∈ projected P i a}
  zero_mem' := fun i => (projected P i a).zero_mem
  add_mem' := fun hv hw i => (projected P i a).add_mem (hv i) (hw i)
  smul_mem' := fun c _ hv i => (projected P i a).smul_mem c (hv i)

end Lax342547.TableSpaces
end

-- Lax342547.SmallTables
section
namespace Lax342547.SmallTables

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

variable {Comp B H N : Type}

structure Table (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) where
  forward : ∀ e, tableSpace P (e, true) →ₗ[Binary] tableSpace Q (e, false) →ₗ[Binary] Binary
  reverse : ∀ e, tableSpace Q (e, true) →ₗ[Binary] tableSpace P (e, false) →ₗ[Binary] Binary

variable [Fintype N] {ΩA ΩB : Type}

end Lax342547.SmallTables
end

-- Lax342547.HoleRelation
section
namespace Lax342547
end Lax342547

namespace Lax342547.HoleRelation
end Lax342547.HoleRelation

namespace Lax342547.HoleRelation.HoleData
end Lax342547.HoleRelation.HoleData
end

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm
end Lax342547.GradientForm
end

-- Lax342547.CutProfiles
section
namespace Lax342547.CutProfiles
end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry
end Lax342547.TagGeometry

namespace Lax342547.TagGeometry.allowedBase
end Lax342547.TagGeometry.allowedBase

namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase
end

-- Lax342547.ConcreteGeometry
section
namespace Lax342547.ConcreteGeometry
end Lax342547.ConcreteGeometry

namespace Lax342547.ConcreteGeometry.changeZ
end Lax342547.ConcreteGeometry.changeZ
end

-- Lax342547.TensorContractions
section
namespace Lax342547.TensorContractions
end Lax342547.TensorContractions
end

-- Lax342547.TableContractions
section
namespace Lax342547.TableContractions

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins

open Lax342547.TableSpaces Lax342547.SmallTables

structure CrossForms (Comp B H : Type) where
  forward : Comp → LinearMap.BilinForm Binary ((Fin 2 × (B ⊕ H)) → Binary)
  reverse : Comp → LinearMap.BilinForm Binary ((Fin 2 × (B ⊕ H)) → Binary)

def Extends {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (F : CrossForms Comp B H) (T : Table P Q) : Prop :=
  (∀ e (v : tableSpace P (e, true)) (w : tableSpace Q (e, false)),
    F.forward e v.val w.val = T.forward e v w) ∧
  (∀ e (v : tableSpace Q (e, true)) (w : tableSpace P (e, false)),
    F.reverse e v.val w.val = T.reverse e v w)

noncomputable def fullPlus {Comp B H : Type} (F : CrossForms Comp B H) (e : Comp) (i z : Fin 2) :
    (B → Binary) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => F.forward e (primalEmbedding i v) (channelEmbedding z (Pi.single h 1))
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

end Lax342547.TableContractions
end
