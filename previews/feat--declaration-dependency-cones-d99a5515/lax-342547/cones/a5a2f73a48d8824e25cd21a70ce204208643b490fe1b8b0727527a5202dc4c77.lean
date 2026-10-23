-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.DeriveFintype

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.LowRankCounting
section
namespace Lax342547.LowRankCounting
end Lax342547.LowRankCounting
end

-- Lax342547.CorankCounting
section
namespace Lax342547.CorankCounting
end Lax342547.CorankCounting
end

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw

def familyMap {K T : Type} [Field K] {V W : T → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) : (∀ i, V i) →ₗ[K] (∀ i, W i) :=
  LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))

open Lax342547.MomentSpace

open scoped ENNReal

end Lax342547.FiniteLinearLaw
end

-- Lax342547.MixerCompatibility
section
namespace Lax342547.MixerCompatibility

variable {K I E F : Type} [Field K] [Fintype I] [Fintype E] [Fintype F]

def restrictions (Z : Matrix I E K) (W : Matrix I F K) :
    Matrix I I K →ₗ[K] Matrix E I K × Matrix I F K where
  toFun L := (Z.transpose * L, L * W)
  map_add' L M := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c L := by simp [Matrix.mul_smul, Matrix.smul_mul]

end Lax342547.MixerCompatibility
end

-- Lax342547.MixerRowLaw
section
namespace Lax342547.MixerRowLaw

variable {K I E F N : Type} [Field K] [Fintype I]

def directions (D : Matrix I N K) :
    (Matrix E I K × Matrix I F K) →ₗ[K] (Matrix E N K × Matrix N F K) where
  toFun p := (p.1 * D, D.transpose * p.2)
  map_add' x y := by simp [Matrix.add_mul, Matrix.mul_add]
  map_smul' c x := by simp [Matrix.smul_mul, Matrix.mul_smul]

def observations (Z : Matrix I E K) (W : Matrix I F K) (D : Matrix I N K) :
    Matrix I I K →ₗ[K] (Matrix E N K × Matrix N F K) :=
  (directions D).comp (MixerCompatibility.restrictions Z W)

open Lax342547.MomentSpace

open scoped ENNReal

end Lax342547.MixerRowLaw
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

-- Lax342547.AtomDirections
section
namespace Lax342547.AtomDirections
end Lax342547.AtomDirections
end

-- Lax342547.RawFrames
section
namespace Lax342547.RawFrames
end Lax342547.RawFrames

namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame
end

-- Lax342547.ConcreteCut
section
namespace Lax342547.ConcreteCut
end Lax342547.ConcreteCut

namespace Lax342547.ConcreteCut.Testers
end Lax342547.ConcreteCut.Testers
end

-- Lax342547.Atoms
section
namespace Lax342547.Atoms
end Lax342547.Atoms

namespace Lax342547.Atoms.Flavor
end Lax342547.Atoms.Flavor

namespace Lax342547.Atoms.retained
end Lax342547.Atoms.retained

namespace Lax342547.Atoms.testerSummary
end Lax342547.Atoms.testerSummary

namespace Lax342547.Atoms.Flavor.generic
end Lax342547.Atoms.Flavor.generic

namespace Lax342547.Atoms.Flavor.pure
end Lax342547.Atoms.Flavor.pure

namespace Lax342547.Atoms.Flavor.sharedOnly
end Lax342547.Atoms.Flavor.sharedOnly
end

-- Lax342547.FormalQuadratic
section
namespace Lax342547.FormalQuadratic

variable {K B : Type} [Field K] [Fintype B] {V : B → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

abbrev Rows (V : B → Type) := ∀ i, V i × V i

open Lax342547.MomentSpace

end Lax342547.FormalQuadratic
end

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.UnaryMixer
section
namespace Lax342547.UnaryMixer

open Lax342547.MomentSpace

variable {E I : Type} [Fintype E] [Fintype I]

abbrev Block (inc : Finset E) (J : ℕ) :=
  (Fin J × E × {f : E // f ∈ inc}) ⊕ (Fin J × {e : E // e ∈ inc} × E)

def blockRank (r : E → ℕ) {inc : Finset E} {J : ℕ} : Block inc J → ℕ
  | .inl (_, e, _) => r e
  | .inr (_, _, f) => r f

abbrev Rows (r : E → ℕ) (inc : Finset E) (J : ℕ) :=
  FormalQuadratic.Rows (fun t : Block inc J => Fin (blockRank r t) → Binary)

noncomputable def rowMap {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary)
    (L R : Fin J → E → E → Matrix I I Binary) : (I → Binary) →ₗ[Binary] Rows r inc J :=
  LinearMap.pi fun t => match t with
    | .inl (j, e, f) =>
        ((Z e).transpose * L j e f.val).mulVecLin.prod
          ((Z e).transpose * R j e f.val).mulVecLin
    | .inr (j, e, f) =>
        ((L j e.val f * Z f).transpose).mulVecLin.prod
          ((R j e.val f * Z f).transpose).mulVecLin

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut

open Lax342547.CutProfiles Lax342547.Atoms

end Lax342547.UnaryMixer
end

-- Lax342547.UnaryRowLaw
section
namespace Lax342547.UnaryRowLaw

open Lax342547.MomentSpace Lax342547.UnaryMixer

variable {E I N : Type} [Fintype E] [Fintype I] [Fintype N]

abbrev Index (E : Type) (J : ℕ) := Bool × Fin J × E × E

abbrev RowIndex (r : E → ℕ) (inc : Finset E) (J : ℕ) :=
  (t : Block inc J) × (Fin (blockRank r t) ⊕ Fin (blockRank r t))

abbrev FullList (r : E → ℕ) (J : ℕ) (N : Type) :=
  ∀ p : Index E J, Matrix (Fin (r p.2.2.1)) N Binary × Matrix N (Fin (r p.2.2.2)) Binary

def fullObservations {r : E → ℕ} {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary) :
    (Index E J → Matrix I I Binary) →ₗ[Binary] FullList r J N :=
  FiniteLinearLaw.familyMap (fun p => MixerRowLaw.observations (Z p.2.2.1) (Z p.2.2.2) D)

def pack {r : E → ℕ} (inc : Finset E) {J : ℕ} :
    FullList r J N →ₗ[Binary] Matrix (RowIndex r inc J) N Binary where
  toFun y a i := match a with
    | ⟨.inl (j, e, f), .inl h⟩ => (y (false, j, e, f.val)).1 h i
    | ⟨.inl (j, e, f), .inr h⟩ => (y (true, j, e, f.val)).1 h i
    | ⟨.inr (j, e, f), .inl h⟩ => (y (false, j, e.val, f)).2 i h
    | ⟨.inr (j, e, f), .inr h⟩ => (y (true, j, e.val, f)).2 i h
  map_add' x y := by
    funext a i
    rcases a with ⟨⟨j, e, f⟩ | ⟨j, e, f⟩, a | a⟩ <;> rfl
  map_smul' c x := by
    funext a i
    rcases a with ⟨⟨j, e, f⟩ | ⟨j, e, f⟩, a | a⟩ <;> rfl

def mixerRows {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary) :
    (Index E J → Matrix I I Binary) →ₗ[Binary] Matrix (RowIndex r inc J) N Binary :=
  (pack inc).comp (fullObservations Z D)

noncomputable def rowLinear {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (M : Index E J → Matrix I I Binary) : (N → Binary) →ₗ[Binary] Rows r inc J :=
  (rowMap inc Z (fun j e f => M (false, j, e, f))
    (fun j e f => M (true, j, e, f))).comp D.mulVecLin

axiom mixerRows_rank {r : E → ℕ} (inc : Finset E) {J : ℕ}
    (Z : ∀ e, Matrix I (Fin (r e)) Binary) (D : Matrix I N Binary)
    (M : Index E J → Matrix I I Binary) :
    (mixerRows inc Z D M).rank = Module.finrank Binary (LinearMap.range (rowLinear inc Z D M))

open scoped ENNReal

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut Lax342547.CutProfiles

end Lax342547.UnaryRowLaw
end
