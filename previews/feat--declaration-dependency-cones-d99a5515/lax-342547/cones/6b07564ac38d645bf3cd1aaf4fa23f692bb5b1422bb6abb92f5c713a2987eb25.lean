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
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Projection
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

-- Lax342547.FrozenBaselines
section
namespace Lax342547.FrozenBaselines

open Lax342547.MomentSpace

variable {V W : Type} [AddCommGroup V] [Module Binary V]
  [AddCommGroup W] [Module Binary W]

structure Splitting (J D Keys : Submodule Binary V) where
  frozen : V →ₗ[Binary] V
  table : V →ₗ[Binary] J
  frozen_fixed : ∀ v ∈ D ⊔ Keys, frozen v = v
  table_zero : ∀ v ∈ D ⊔ Keys, table v = 0
  frozen_table : ∀ v : J, frozen v.val ∈ D
  table_sum : ∀ v : J, frozen v.val + (table v.val).val = v.val

def baseline {J D Keys : Submodule Binary V} {J' D' Keys' : Submodule Binary W}
    (S : Splitting J D Keys) (S' : Splitting J' D' Keys')
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary) :
    V →ₗ[Binary] W →ₗ[Binary] Binary :=
  A.compl₁₂ S.frozen LinearMap.id + A.compl₁₂ LinearMap.id S'.frozen -
    A.compl₁₂ S.frozen S'.frozen + T.compl₁₂ S.table S'.table

def Compatible (J D : Submodule Binary V) (J' D' : Submodule Binary W)
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary) : Prop :=
  ∀ v : J, ∀ w : J', v.val ∈ D ∨ w.val ∈ D' → T v w = A v.val w.val

def ExtendsFrozen (D Keys : Submodule Binary V) (D' Keys' : Submodule Binary W)
    (A B : V →ₗ[Binary] W →ₗ[Binary] Binary) : Prop :=
  ∀ v w, v ∈ D ⊔ Keys ∨ w ∈ D' ⊔ Keys' → B v w = A v w

end Lax342547.FrozenBaselines
end

-- Lax342547.PrimalRetractions
section
namespace Lax342547.PrimalRetractions
end Lax342547.PrimalRetractions
end

-- Lax342547.BaselineRank
section
namespace Lax342547.BaselineRank
end Lax342547.BaselineRank
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

noncomputable def rank [Fintype Axis] (P : Pin Axis I N) : ℕ :=
  ∑ a, Module.finrank Binary (P.space a)

end Pin

end Lax342547.ExactPins
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

-- Lax342547.NominalPrimal
section
namespace Lax342547.NominalPrimal

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

variable {Comp B H N : Type}

def primal : Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary) where
  carrier := {v | ∀ i h, v (i, Sum.inr h) = 0}
  zero_mem' := by intro i h; rfl
  add_mem' := by intro v w hv hw i h; change v (i, Sum.inr h) + w (i, Sum.inr h) = 0; rw [hv, hw, add_zero]
  smul_mem' := by intro c v hv i h; change c * v (i, Sum.inr h) = 0; rw [hv, mul_zero]

end Lax342547.NominalPrimal
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

-- Lax342547.SmallTables
section
namespace Lax342547.SmallTables
end Lax342547.SmallTables

namespace Lax342547.SmallTables.Table
end Lax342547.SmallTables.Table
end

-- Lax342547.NominalBaselines
section
namespace Lax342547.NominalBaselines

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.TableSpaces

open Lax342547.SmallTables Lax342547.NominalPrimal Lax342547.FrozenBaselines

axiom nominal_baseline {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a b : Comp × Bool)
    (Keys Keys' : Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary)) (K : ℕ)
    (hP : P.rank ≤ K) (hQ : Q.rank ≤ K)
    (hkey : Keys ≤ primal) (hkey' : Keys' ≤ primal)
    (hcard : Module.finrank Binary Keys ≤ 28) (hcard' : Module.finrank Binary Keys' ≤ 28)
    (hfresh : Disjoint (tableSpace P a) Keys) (hfresh' : Disjoint (tableSpace Q b) Keys')
    (A : ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary]
      ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] Binary)
    (T : tableSpace P a →ₗ[Binary] tableSpace Q b →ₗ[Binary] Binary)
    (h : Compatible (tableSpace P a) (P.space a) (tableSpace Q b) (Q.space b) A T) :
    ∃ F : ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary]
        ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] Binary,
      ExtendsFrozen (P.space a) Keys (Q.space b) Keys' A F ∧
      (∀ v : tableSpace P a, ∀ w : tableSpace Q b, F v.val w.val = T v w) ∧
      ∀ z : Fin 2,
        Module.finrank Binary (LinearMap.range
          (F.compl₁₂ (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range
          (F.flip.compl₁₂ (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ 3 * K + 28

end Lax342547.NominalBaselines
end
