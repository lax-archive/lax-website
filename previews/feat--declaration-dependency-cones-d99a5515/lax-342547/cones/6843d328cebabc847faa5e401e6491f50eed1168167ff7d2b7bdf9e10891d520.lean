-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
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
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
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
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm

open Lax342547.MomentSpace

variable {X Tag : Type} [AddCommGroup X] [Module Binary X] [Fintype Tag]

def rankOne (a b : X →ₗ[Binary] Binary) : LinearMap.BilinForm Binary X := a.smulRight b

end Lax342547.GradientForm
end

-- Lax342547.CutProfiles
section
namespace Lax342547.CutProfiles
end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry.allowedBase
end Lax342547.TagGeometry.allowedBase

namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase

namespace Lax342547.TagGeometry

open Lax342547.MomentSpace

abbrev Tag (k : ℕ) := ZMod (2 * k + 1)

abbrev Base (k n : ℕ) := ((Tag k × Tag k) × Fin n) ⊕ (Fin 3 × Fin n)

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

def shared {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (0, i)

def sharp {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (1, i)

def emptySelector (b degree : ℕ) : SelectorCoordinates b degree := ⟨∅, Nat.zero_le _⟩

def bitSelector {b degree : ℕ} (h : 1 ≤ degree) (a : Fin b) : SelectorCoordinates b degree :=
  ⟨{a}, by simpa using h⟩

def pairLeft {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val, by omega⟩

def pairRight {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val + 1, by omega⟩

def matrixEntry {I : Type} (i j : I) : Matrix I I Binary →ₗ[Binary] Binary where
  toFun w := w i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blockForm {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ ρ : Fin r, GradientForm.rankOne
    (LinearMap.proj (emptySelector b degree, some (c (pairLeft h ρ))))
    (LinearMap.proj (emptySelector b degree, some (c (pairRight h ρ))))

def sharpForm {k n b degree : ℕ} (h : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ a : Fin b, ∑ i : Fin n, ∑ j : Fin n, M a i j •
    (GradientForm.rankOne (LinearMap.proj (bitSelector h a, some (sharp i)))
      (LinearMap.proj (emptySelector b degree, some (sharp j))) +
    GradientForm.rankOne (LinearMap.proj (emptySelector b degree, some (sharp i)))
      (LinearMap.proj (bitSelector h a, some (sharp j))))

def matrixPair {I : Type} [Fintype I] (E : Matrix I I Binary) :
    Matrix I I Binary →ₗ[Binary] Binary :=
  ∑ i, ∑ j, E i j • matrixEntry i j

end Lax342547.ConcreteGeometry
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

open Lax342547.MomentSpace Lax342547.ConcreteGeometry

open Lax342547.BaseMoments Lax342547.SelectedMoments

def dualCoordinates {I : Type} [DecidableEq I] :
    Module.Dual Binary (I → Binary) →ₗ[Binary] (I → Binary) where
  toFun φ i := φ (Pi.single i 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def pureContraction {I : Type} [Fintype I]
    (S T : Submodule Binary (I → Binary))
    (β : ((I → Binary) ⧸ S) →ₗ[Binary] ((I → Binary) ⧸ T) →ₗ[Binary] Binary) :
    Matrix I I Binary →ₗ[Binary] Binary := by
  classical
  exact matrixPair (LinearMap.BilinForm.toMatrix' (β.compl₁₂ S.mkQ T.mkQ))

def PureAnnihilates {I : Type} [Fintype I] (M : Matrix I I Binary)
    (S T : Submodule Binary (I → Binary)) : Prop :=
  ∀ β, pureContraction S T β M = 0

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
end Lax342547.ExactPins

namespace Lax342547.ExactPins.Pin
end Lax342547.ExactPins.Pin
end

-- Lax342547.ProjectedPins
section
namespace Lax342547.ProjectedPins
end Lax342547.ProjectedPins
end

-- Lax342547.TableSpaces
section
namespace Lax342547.TableSpaces
end Lax342547.TableSpaces
end

-- Lax342547.PairedAnnihilators
section
namespace Lax342547.PairedAnnihilators
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
namespace Lax342547.WitnessAtoms
end Lax342547.WitnessAtoms

namespace Lax342547.WitnessAtoms.Numerical
end Lax342547.WitnessAtoms.Numerical

namespace Lax342547.WitnessAtoms.PointAtom
end Lax342547.WitnessAtoms.PointAtom
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
namespace Lax342547.PairedWitnesses
end Lax342547.PairedWitnesses

namespace Lax342547.PairedWitnesses.Lists
end Lax342547.PairedWitnesses.Lists

namespace Lax342547.PairedWitnesses.ScalarRecipe
end Lax342547.PairedWitnesses.ScalarRecipe
end

-- Lax342547.PairedRecipes
section
namespace Lax342547.PairedRecipes
end Lax342547.PairedRecipes
end

-- Lax342547.PairedKeys
section
namespace Lax342547.PairedKeys
end Lax342547.PairedKeys
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

-- Lax342547.FrozenCharacters
section
namespace Lax342547.FrozenCharacters

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TensorAnnihilators

axiom zero_quotient_frozen_agreement {I : Type} [Fintype I]
    (C : Matrix I I Binary) (D E : Submodule Binary (I → Binary))
    (F G : (I → Binary) →ₗ[Binary] (I → Binary) →ₗ[Binary] Binary)
    (hC : PureAnnihilates C D E)
    (hD : ∀ v ∈ D, ∀ w, F v w = G v w)
    (hE : ∀ v w, w ∈ E → F v w = G v w) :
    by
      classical
      exact matrixPair (LinearMap.BilinForm.toMatrix' F) C =
        matrixPair (LinearMap.BilinForm.toMatrix' G) C

end Lax342547.FrozenCharacters
end
