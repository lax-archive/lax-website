-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.DeriveFintype

-- Lax342547.HoleRelation
section
namespace Lax342547
end Lax342547

namespace Lax342547.HoleRelation
end Lax342547.HoleRelation

namespace Lax342547.HoleRelation.HoleData
end Lax342547.HoleRelation.HoleData
end

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

instance (b degree : ℕ) : Fintype (SelectorCoordinates b degree) :=
  inferInstanceAs (Fintype {S : Finset (Fin b) // S.card ≤ degree})

def selectorEval {b degree : ℕ} (s : Fin b → Binary)
    (c : SelectorCoordinates b degree) : Binary := ∏ i ∈ c.val, s i

variable {Label Coord Base : Type}

def baseEval (z : Base → Binary) : Option Base → Binary
  | none => 1
  | some i => z i

def point (p : Label → Coord → Binary) (s : Label) (z : Base → Binary)
    (i : Coord × Option Base) : Binary := p s i.1 * baseEval z i.2

def pointMoment (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    Matrix (Coord × Option Base) (Coord × Option Base) Binary :=
  fun i j => point p s z i * point p s z j

end Lax342547.MomentSpace
end

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm
end Lax342547.GradientForm
end

-- Lax342547.CutProfiles
section
namespace Lax342547.CutProfiles

open Lax342547.MomentSpace

def Component (Tag : Type) := {e : Finset Tag // e.card = 2}

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase

namespace Lax342547.TagGeometry

open Lax342547.MomentSpace

abbrev Tag (k : ℕ) := ZMod (2 * k + 1)

def interval (k : ℕ) (d : Tag k) : Finset (Tag k) :=
  Finset.univ.image (fun i : Fin k => d + (i.val + 1 : ℕ))

abbrev Base (k n : ℕ) := ((Tag k × Tag k) × Fin n) ⊕ (Fin 3 × Fin n)

def allowedBase (k n : ℕ) (l : Tag k) : Set (Base k n)
  | Sum.inl ((d, _), _) => l ∈ interval k d
  | Sum.inr _ => True

end Lax342547.TagGeometry
end

-- Lax342547.ConcreteGeometry
section
namespace Lax342547.ConcreteGeometry.changeZ
end Lax342547.ConcreteGeometry.changeZ

namespace Lax342547.ConcreteGeometry

open Lax342547.MomentSpace Lax342547.TagGeometry

abbrev Coordinate (k n b degree : ℕ) := SelectorCoordinates b degree × Option (Base k n)

abbrev Moment (k n b degree : ℕ) := Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary

def ordinary {k n : ℕ} (d t : Tag k) (i : Fin n) : Base k n := Sum.inl ((d, t), i)

def shared {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (0, i)

def emptySelector (b degree : ℕ) : SelectorCoordinates b degree := ⟨∅, Nat.zero_le _⟩

def pairLeft {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val, by omega⟩

def pairRight {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val + 1, by omega⟩

def matrixEntry {I : Type} (i j : I) : Matrix I I Binary →ₗ[Binary] Binary where
  toFun w := w i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blockTester {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    Moment k n b degree →ₗ[Binary] Binary :=
  ∑ ρ : Fin r, matrixEntry (emptySelector b degree, some (c (pairLeft h ρ)))
    (emptySelector b degree, some (c (pairRight h ρ)))

def etaO {k n b degree r : ℕ} (h : 2 * r ≤ n) : Moment k n b degree →ₗ[Binary] Binary :=
  ∑ d : Tag k, ∑ t : Tag k, blockTester h (ordinary d t)

def eta {k n b degree r : ℕ} (h : 2 * r ≤ n) : Moment k n b degree →ₗ[Binary] Binary :=
  etaO h + blockTester h shared

end Lax342547.ConcreteGeometry
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

-- Lax342547.ConcreteCut
section
namespace Lax342547.ConcreteCut
end Lax342547.ConcreteCut

namespace Lax342547.ConcreteCut.Testers
end Lax342547.ConcreteCut.Testers
end

-- Lax342547.SelectorInterpolation
section
namespace Lax342547.SelectorInterpolation
end Lax342547.SelectorInterpolation
end

-- Lax342547.SparsePins
section
namespace Lax342547.SparsePins
end Lax342547.SparsePins
end

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.QuotientRank
section
namespace Lax342547.QuotientRank
end Lax342547.QuotientRank
end

-- Lax342547.BaseMoments
section
namespace Lax342547.BaseMoments
end Lax342547.BaseMoments
end

-- Lax342547.SelectedMoments
section
namespace Lax342547.SelectedMoments
end Lax342547.SelectedMoments
end

-- Lax342547.TensorAnnihilators
section
namespace Lax342547.TensorAnnihilators
end Lax342547.TensorAnnihilators
end

-- Lax342547.TensorBlocks
section
namespace Lax342547.TensorBlocks
end Lax342547.TensorBlocks
end

-- Lax342547.LabelRelations
section
namespace Lax342547.LabelRelations
end Lax342547.LabelRelations
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

-- Lax342547.ProjectedPins
section
namespace Lax342547.ProjectedPins
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

def channelProjection {B H : Type} (i : Fin 2) :
    ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (H → Binary) where
  toFun v h := v (i, Sum.inr h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def channelEmbedding {B H : Type} (i : Fin 2) :
    (H → Binary) →ₗ[Binary] ((Fin 2 × (B ⊕ H)) → Binary) where
  toFun v x := if x.1 = i then Sum.elim (fun _ => 0) v x.2 else 0
  map_add' v w := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]
  map_smul' c v := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]

def protectedChannel {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (a : Comp × Bool) :
    Submodule Binary (H → Binary) := (P.space a).map (channelProjection i)

end Lax342547.TableSpaces
end

-- Lax342547.PairedAnnihilators
section
namespace Lax342547.PairedAnnihilators

open Lax342547.MomentSpace Lax342547.ConcreteGeometry

open Lax342547.ProjectedPins Lax342547.TableSpaces Lax342547.TensorAnnihilators

abbrev Nominal (B H : Type) := (Fin 2 × (B ⊕ H)) → Binary

end Lax342547.PairedAnnihilators
end

-- Lax342547.FreshKeys
section
namespace Lax342547.FreshKeys
end Lax342547.FreshKeys
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

-- Lax342547.NominalPrimal
section
namespace Lax342547.NominalPrimal
end Lax342547.NominalPrimal
end

-- Lax342547.KeySpans
section
namespace Lax342547.KeySpans

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.TableSpaces

variable {Base Comp H N : Type} {b degree : ℕ}

def ray {I : Fin 2 → Type} (label : ∀ i, I i → Fin b → Binary)
    (base : ∀ i, I i → Base → Binary) (x : Σ i, I i) :
    (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) → Binary :=
  primalEmbedding x.1 (point (selectorEval (degree := degree)) (label x.1 x.2) (base x.1 x.2))

end Lax342547.KeySpans
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

-- Lax342547.BinaryPrescriptions
section
namespace Lax342547.BinaryPrescriptions
end Lax342547.BinaryPrescriptions
end

-- Lax342547.WitnessAtoms
section
namespace Lax342547.WitnessAtoms.Numerical
end Lax342547.WitnessAtoms.Numerical

namespace Lax342547.WitnessAtoms

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.Atoms

structure PointAtom (k n b degree : ℕ) where
  tag : Tag k
  label : Fin b → Binary
  base : Base k n → Binary
  supported : ∀ i, i ∉ allowedBase k n tag → base i = 0

end Lax342547.WitnessAtoms
end

-- Lax342547.AtomProducts
section
namespace Lax342547.AtomProducts
end Lax342547.AtomProducts
end

-- Lax342547.SymmetricPrescriptions
section
namespace Lax342547.SymmetricPrescriptions
end Lax342547.SymmetricPrescriptions
end

-- Lax342547.RecipeRows
section
namespace Lax342547.RecipeRows
end Lax342547.RecipeRows
end

-- Lax342547.ConcreteRecipes
section
namespace Lax342547.ConcreteRecipes
end Lax342547.ConcreteRecipes
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

open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.RawFrames

open scoped ENNReal

def jointMatrix {Draw I N : Type} (A : Draw → Matrix N I Binary) : Matrix N (Draw × I) Binary :=
  fun n j => A j.1 n j.2

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

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

open Lax342547.ProductImages Lax342547.ExactPins

open scoped ENNReal

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]

def observationMatrix {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : Matrix N (Fin 2 × (B ⊕ H)) Binary :=
  if a.2 then jointMatrix (fun i => (plus (o i a.1)).val)
  else jointMatrix (fun i => (minus (o i a.1)).val)

def observation {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary) :=
  (observationMatrix o a).mulVecLin

end Lax342547.ReferencePins
end

-- Lax342547.SmallTables
section
namespace Lax342547.SmallTables
end Lax342547.SmallTables

namespace Lax342547.SmallTables.Table
end Lax342547.SmallTables.Table
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

end Lax342547.TableContractions
end

-- Lax342547.RawContractions
section
namespace Lax342547.RawContractions

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins Lax342547.ProjectedPins

open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableContractions

open Lax342547.ReferencePins

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N] {E : Matrix B B Binary}

def rawForms (oA oB : Fin 2 → Comp → Frame B H N E) : CrossForms Comp B H :=
  ⟨fun e => (dotProductBilin Binary Binary).compl₁₂ (observation oA (e, true))
      (observation oB (e, false)),
    fun e => (dotProductBilin Binary Binary).compl₁₂ (observation oB (e, true))
      (observation oA (e, false))⟩

end Lax342547.RawContractions
end

-- Lax342547.PairedWitnesses
section
namespace Lax342547.PairedWitnesses.ScalarRecipe
end Lax342547.PairedWitnesses.ScalarRecipe

namespace Lax342547.PairedWitnesses

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.Atoms Lax342547.WitnessAtoms

open Lax342547.RawFrames Lax342547.ExactPins Lax342547.ProjectedPins

open Lax342547.SmallTables Lax342547.TableContractions

def diagonalBit {k n b degree r : ℕ} (hr : 2 * r ≤ n) (x : PointAtom k n b degree) : Binary :=
  eta hr (pointMoment (selectorEval (degree := degree)) x.label x.base)

structure Lists (k n b degree r : ℕ) (hr : 2 * r ≤ n) where
  length : Fin 2 → Fin 2 → ℕ
  positive : ∀ i z, 1 ≤ length i z
  short : ∀ i z, length i z ≤ 7
  left : ∀ i z, Fin (length i z) → PointAtom k n b degree
  right : ∀ i z, Fin (length i z) → PointAtom k n b degree
  same_tag : ∀ i z t, (left i z t).tag = (right i z t).tag
  same_diagonal : ∀ i z t, diagonalBit hr (left i z t) = diagonalBit hr (right i z t)
  left_fresh : ∀ i, Function.Injective (fun t : Σ z, Fin (length i z) => (left i t.1 t.2).label)
  right_fresh : ∀ z, Function.Injective (fun t : Σ i, Fin (length i z) => (right t.1 z t.2).label)

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}

variable {H N : Type} [Fintype H] [Fintype N]
  {E : Moment k n b degree}

abbrev Unit := Fin 2 → Component (Tag k) → Frame (Coordinate k n b degree) H N E

end Lax342547.PairedWitnesses
end

-- Lax342547.PairedRecipes
section
namespace Lax342547.PairedRecipes

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.WitnessAtoms

open Lax342547.PairedWitnesses Lax342547.ConcreteRecipes

open Lax342547.ExactPins Lax342547.SmallTables Lax342547.TableContractions

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}

def flip (W : Lists k n b degree r hr) : Lists k n b degree r hr where
  length i z := W.length z i
  positive i z := W.positive z i
  short i z := W.short z i
  left i z := W.right z i
  right i z := W.left z i
  same_tag i z t := (W.same_tag z i t).symm
  same_diagonal i z t := (W.same_diagonal z i t).symm
  left_fresh := W.right_fresh
  right_fresh := W.left_fresh

variable {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

end Lax342547.PairedRecipes
end

-- Lax342547.PairedKeys
section
namespace Lax342547.PairedKeys

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.PairedRecipes

open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.NominalPrimal Lax342547.KeySpans

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

abbrev Positions (W : Lists k n b degree r hr) := Σ i, Σ z, Fin (W.length i z)

def labels (W : Lists k n b degree r hr) (i : Fin 2) (x : Σ z, Fin (W.length i z)) :=
  (W.left i x.1 x.2).label

def bases (W : Lists k n b degree r hr) (i : Fin 2) (x : Σ z, Fin (W.length i z)) :=
  (W.left i x.1 x.2).base

noncomputable def direction (W : Lists k n b degree r hr) (e : Component (Tag k))
    (x : Positions W) : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary := by
  classical
  exact if (W.left x.1 x.2.1 x.2.2).tag ∈ e.val then ray (labels W) (bases W) x else 0

def keys (W : Lists k n b degree r hr) (e : Component (Tag k)) :
    Submodule Binary ((Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary) :=
  Submodule.span Binary (Set.range (direction (H := H) W e))

end Lax342547.PairedKeys
end

-- Lax342547.BarredSpaces
section
namespace Lax342547.BarredSpaces

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.PairedKeys

open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

open Lax342547.PairedAnnihilators

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

def barred (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Component (Tag k) × Bool) :
    Submodule Binary (Nominal (Coordinate k n b degree) H) :=
  P.space a ⊔ keys (H := H) W a.1 ⊔ ⨆ z, (U z).map (channelEmbedding z)

end Lax342547.BarredSpaces
end

-- Lax342547.LabelDecomposition
section
namespace Lax342547.LabelDecomposition
end Lax342547.LabelDecomposition
end

-- Lax342547.PureObstructions
section
namespace Lax342547.PureObstructions
end Lax342547.PureObstructions
end

-- Lax342547.PinLabelExclusions
section
namespace Lax342547.PinLabelExclusions
end Lax342547.PinLabelExclusions
end

-- Lax342547.QuotientExtractors
section
namespace Lax342547.QuotientExtractors
end Lax342547.QuotientExtractors
end

-- Lax342547.SelectedBlocks
section
namespace Lax342547.SelectedBlocks
end Lax342547.SelectedBlocks
end

-- Lax342547.SelectedScalars
section
namespace Lax342547.SelectedScalars
end Lax342547.SelectedScalars
end

-- Lax342547.SelectedRemoval
section
namespace Lax342547.SelectedRemoval
end Lax342547.SelectedRemoval
end

-- Lax342547.ResidualLabels
section
namespace Lax342547.ResidualLabels
end Lax342547.ResidualLabels
end

-- Lax342547.SparseKeyCoefficients
section
namespace Lax342547.SparseKeyCoefficients
end Lax342547.SparseKeyCoefficients
end

-- Lax342547.BarredElimination
section
namespace Lax342547.BarredElimination
end Lax342547.BarredElimination
end

-- Lax342547.PrimalContractions
section
namespace Lax342547.PrimalContractions
end Lax342547.PrimalContractions
end

-- Lax342547.ChannelChanges
section
namespace Lax342547.ChannelChanges

open Lax342547.MomentSpace Lax342547.TableSpaces Lax342547.PairedAnnihilators

open Lax342547.PrimalContractions Lax342547.ExactPins Lax342547.ProjectedPins

open Lax342547.SmallTables Lax342547.TableContractions

open Lax342547.TensorAnnihilators

def perpendicular {H : Type} [Fintype H] (S : Submodule Binary (H → Binary)) :
    Submodule Binary (H → Binary) :=
  LinearMap.BilinForm.orthogonal (dotProductBilin Binary Binary) S

def channelChange {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z : Fin 2) :
    LinearMap.BilinForm Binary (Nominal B H) :=
  (dotProductBilin Binary Binary).compl₁₂
    (((perpendicular S).subtype.comp δ).comp D.mkQ) (channelProjection z)

end Lax342547.ChannelChanges
end

-- Lax342547.DerivativeResponses
section
namespace Lax342547.DerivativeResponses

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses

open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.PairedAnnihilators

open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions

open Lax342547.SelectedRemoval

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]

abbrev PlusParameters (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) (z : Fin 2) :=
  ∀ e, (Nominal (Coordinate k n b degree) H ⧸ barred W P (U e) (e, true)) →ₗ[Binary]
    perpendicular (protectedChannel Q z (e, false))

abbrev MinusParameters (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) (z : Fin 2) :=
  ∀ e, (Nominal (Coordinate k n b degree) H ⧸ barred W P (V e) (e, false)) →ₗ[Binary]
    perpendicular (protectedChannel Q z (e, true))

end Lax342547.DerivativeResponses
end

-- Lax342547.EffectiveObstructions
section
namespace Lax342547.EffectiveObstructions
end Lax342547.EffectiveObstructions
end

-- Lax342547.NominalBaselines
section
namespace Lax342547.NominalBaselines
end Lax342547.NominalBaselines
end

-- Lax342547.RawBaselines
section
namespace Lax342547.RawBaselines

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles

open Lax342547.PairedWitnesses Lax342547.PairedRecipes Lax342547.PairedKeys

open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.SmallTables

open Lax342547.TableContractions Lax342547.RawContractions Lax342547.ReferencePins

open Lax342547.NominalPrimal Lax342547.FrozenBaselines Lax342547.KeySpans

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}
  {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

def Frozen (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (oA oB : Unit (H := H) (N := N) (E := E)) : Prop :=
  ∀ e,
    ExtendsFrozen (P.space (e, true)) (keys W e) (Q.space (e, false)) (keys (flip W) e)
      ((rawForms oA oB).forward e) (F.forward e) ∧
    ExtendsFrozen (Q.space (e, true)) (keys (flip W) e) (P.space (e, false)) (keys W e)
      ((rawForms oA oB).reverse e) (F.reverse e)

end Lax342547.RawBaselines
end

-- Lax342547.FrozenValues
section
namespace Lax342547.FrozenValues
end Lax342547.FrozenValues
end

-- Lax342547.RecipeResiduals
section
namespace Lax342547.RecipeResiduals
end Lax342547.RecipeResiduals
end

-- Lax342547.ResponseSolvability
section
namespace Lax342547.ResponseSolvability
end Lax342547.ResponseSolvability
end

-- Lax342547.BoundedDerivatives
section
namespace Lax342547.BoundedDerivatives
end Lax342547.BoundedDerivatives
end

-- Lax342547.ResponseMatrices
section
namespace Lax342547.ResponseMatrices
end Lax342547.ResponseMatrices
end

-- Lax342547.BaseCompression
section
namespace Lax342547.BaseCompression
end Lax342547.BaseCompression

namespace Lax342547.BaseCompression.blockMap
end Lax342547.BaseCompression.blockMap

namespace Lax342547.BaseCompression.liftBase
end Lax342547.BaseCompression.liftBase
end

-- Lax342547.RankedProjection
section
namespace Lax342547.RankedProjection
end Lax342547.RankedProjection
end

-- Lax342547.ResidualRealization
section
namespace Lax342547.ResidualRealization
end Lax342547.ResidualRealization
end

-- Lax342547.QuotientCompression
section
namespace Lax342547.QuotientCompression
end Lax342547.QuotientCompression

namespace Lax342547.QuotientCompression.nominalLift
end Lax342547.QuotientCompression.nominalLift
end

-- Lax342547.ConstrainedCompression
section
namespace Lax342547.ConstrainedCompression
end Lax342547.ConstrainedCompression

namespace Lax342547.ConstrainedCompression.baseAt
end Lax342547.ConstrainedCompression.baseAt

namespace Lax342547.ConstrainedCompression.blockEmbed
end Lax342547.ConstrainedCompression.blockEmbed

namespace Lax342547.ConstrainedCompression.constantPart
end Lax342547.ConstrainedCompression.constantPart
end

-- Lax342547.CompressedResidual
section
namespace Lax342547.CompressedResidual
end Lax342547.CompressedResidual
end

-- Lax342547.ChannelFactorization
section
namespace Lax342547.ChannelFactorization
end Lax342547.ChannelFactorization
end

-- Lax342547.StarRouting
section
namespace Lax342547.StarRouting
end Lax342547.StarRouting
end

-- Lax342547.TargetTesters
section
namespace Lax342547.TargetTesters
end Lax342547.TargetTesters
end

-- Lax342547.TargetMatrices
section
namespace Lax342547.TargetMatrices
end Lax342547.TargetMatrices
end

-- Lax342547.NonlinearChannels
section
namespace Lax342547.NonlinearChannels
end Lax342547.NonlinearChannels
end

-- Lax342547.RecipeChannels
section
namespace Lax342547.RecipeChannels
end Lax342547.RecipeChannels
end

-- Lax342547.ChannelAssembly
section
namespace Lax342547.ChannelAssembly

open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges

open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions

open Lax342547.DerivativeResponses Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses

open Lax342547.ExactPins Lax342547.BarredSpaces Lax342547.PairedKeys

noncomputable def assemble {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i) :
    CrossForms (Component (Tag k)) (Coordinate k n b degree) H :=
  { forward := fun e => F.forward e +
      (∑ z, channelChange (barred W P (U e) (e, true))
        (protectedChannel Q z (e, false)) (δ z e) z) +
      ∑ i, (channelChange (barred (Lax342547.PairedRecipes.flip W) Q (V' e) (e, false))
        (protectedChannel P i (e, true)) (ε' i e) i).flip
    reverse := fun e => F.reverse e +
      (∑ i, channelChange (barred (Lax342547.PairedRecipes.flip W) Q (U' e) (e, true))
        (protectedChannel P i (e, false)) (δ' i e) i) +
      ∑ z, (channelChange (barred W P (V e) (e, false))
        (protectedChannel Q z (e, true)) (ε z e) z).flip }

end Lax342547.ChannelAssembly
end

-- Lax342547.GradientAssembly
section
namespace Lax342547.GradientAssembly
end Lax342547.GradientAssembly
end

-- Lax342547.FrozenAssembly
section
namespace Lax342547.FrozenAssembly

open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges

open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions

open Lax342547.DerivativeResponses Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses

open Lax342547.ExactPins Lax342547.BarredSpaces Lax342547.PairedKeys

open Lax342547.FrozenBaselines Lax342547.RawBaselines Lax342547.ChannelAssembly

axiom assembled_frozen {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H] [Fintype N]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    {E : Moment k n b degree} (oA oB : Unit (H := H) (N := N) (E := E))
    (hF : Frozen F W P Q oA oB) : Frozen (assemble W P Q U V U' V' F δ ε δ' ε') W P Q oA oB

end Lax342547.FrozenAssembly
end
