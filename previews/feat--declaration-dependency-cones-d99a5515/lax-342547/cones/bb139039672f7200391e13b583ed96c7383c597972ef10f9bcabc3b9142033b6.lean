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

-- Lax342547.ExactPins
section
namespace Lax342547.ExactPins
end Lax342547.ExactPins

namespace Lax342547.ExactPins.Pin
end Lax342547.ExactPins.Pin
end

-- Lax342547.LeafExtraction
section
namespace Lax342547.LeafExtraction
end Lax342547.LeafExtraction
end

-- Lax342547.LeafImages
section
namespace Lax342547.LeafImages
end Lax342547.LeafImages
end

-- Lax342547.SparsePins
section
namespace Lax342547.SparsePins
end Lax342547.SparsePins
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

end Lax342547.TableSpaces
end

-- Lax342547.FreshKeys
section
namespace Lax342547.FreshKeys
end Lax342547.FreshKeys
end

-- Lax342547.FrozenBaselines
section
namespace Lax342547.FrozenBaselines
end Lax342547.FrozenBaselines

namespace Lax342547.FrozenBaselines.Splitting
end Lax342547.FrozenBaselines.Splitting
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

abbrev Vector (k n b degree : ℕ) := Coordinate k n b degree → Binary

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

def PointAtom.vector {k n b degree : ℕ} (x : PointAtom k n b degree) : Vector k n b degree :=
  point selectorEval x.label x.base

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
end Lax342547.TableContractions

namespace Lax342547.TableContractions.CrossForms
end Lax342547.TableContractions.CrossForms
end

-- Lax342547.RawContractions
section
namespace Lax342547.RawContractions
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
end Lax342547.PairedRecipes
end

-- Lax342547.PairedKeys
section
namespace Lax342547.PairedKeys

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.PairedRecipes

open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.NominalPrimal Lax342547.KeySpans

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

def labels (W : Lists k n b degree r hr) (i : Fin 2) (x : Σ z, Fin (W.length i z)) :=
  (W.left i x.1 x.2).label

def bases (W : Lists k n b degree r hr) (i : Fin 2) (x : Σ z, Fin (W.length i z)) :=
  (W.left i x.1 x.2).base

end Lax342547.PairedKeys
end

-- Lax342547.SelectorInterpolation
section
namespace Lax342547.SelectorInterpolation
end Lax342547.SelectorInterpolation
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

-- Lax342547.PairedAnnihilators
section
namespace Lax342547.PairedAnnihilators
end Lax342547.PairedAnnihilators
end

-- Lax342547.BarredSpaces
section
namespace Lax342547.BarredSpaces
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
end Lax342547.ChannelChanges
end

-- Lax342547.DerivativeResponses
section
namespace Lax342547.DerivativeResponses
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

-- Lax342547.QuerySlots
section
namespace Lax342547.QuerySlots

open Lax342547.CutProfiles

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.PairedWitnesses

open Lax342547.StarRouting

abbrev Position {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :=
  Σ i : Fin 2, Σ z : Fin 2, Fin (W.length i z)

end Lax342547.QuerySlots
end

-- Lax342547.ReferenceKeys
section
namespace Lax342547.ReferenceKeys

open Lax342547.MomentSpace

open scoped ENNReal

abbrev Tuples (Comp : Type) (Pos : Comp → Type) (N : Type) :=
  ∀ e, Matrix N (Pos e) Binary × Matrix N (Pos e) Binary

end Lax342547.ReferenceKeys
end

-- Lax342547.QueryReference
section
namespace Lax342547.QueryReference

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.CutProfiles

open Lax342547.PairedWitnesses Lax342547.QuerySlots Lax342547.ReferenceKeys

open Lax342547.ConcreteGeometry

open scoped ENNReal

abbrev ComponentPosition {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (e : Component (Tag k)) :=
  {p : Lax342547.QuerySlots.Position W // (W.left p.1 p.2.1 p.2.2).tag ∈ e.val}

noncomputable def leftTuple {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E)) :
    Tuples (Component (Tag k)) (ComponentPosition W) N := fun e =>
  ⟨fun n p => (o p.val.1 e).P.mulVec (W.left p.val.1 p.val.2.1 p.val.2.2).vector n,
    fun n p => (o p.val.1 e).Q.mulVec (W.left p.val.1 p.val.2.1 p.val.2.2).vector n⟩

end Lax342547.QueryReference
end

-- Lax342547.QueryIndependence
section
namespace Lax342547.QueryIndependence

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.CutProfiles

open Lax342547.PairedWitnesses Lax342547.QueryReference Lax342547.QuerySlots

open Lax342547.PairedKeys Lax342547.KeySpans Lax342547.TableSpaces Lax342547.ExactPins

open Lax342547.ConcreteGeometry

noncomputable def keyMap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H : Type}
    (W : Lists k n b degree r hr) (e : Component (Tag k)) :
    (ComponentPosition W e → Binary) →ₗ[Binary] ((Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary) := by
  classical
  exact
    { toFun := fun c => ∑ p, c p • ray (H := H) (degree := degree) (labels W) (bases W) p.val
      map_add' := by intro c d; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro s c; simp [Finset.smul_sum, smul_smul] }

end Lax342547.QueryIndependence
end

-- Lax342547.RawQueryImages
section
namespace Lax342547.RawQueryImages

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ReferencePins

open Lax342547.TableSpaces Lax342547.ProductImages Lax342547.TagGeometry

open Lax342547.ConcreteGeometry Lax342547.PairedWitnesses Lax342547.QueryReference

open Lax342547.QueryIndependence Lax342547.PairedKeys Lax342547.KeySpans

open scoped ENNReal

axiom key_observations_left {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E))
    (e : Lax342547.CutProfiles.Component (Tag k)) (mode : Bool) : by
      classical
      exact LinearMap.toMatrix' ((observation o (e,mode)).comp (keyMap (H := H) W e)) =
        if mode then (leftTuple W o e).1 else (leftTuple W o e).2

end Lax342547.RawQueryImages
end
