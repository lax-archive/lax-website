-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.DeriveFintype
import Mathlib.Topology.Instances.Real.Lemmas

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

instance (b degree : ℕ) : Fintype (SelectorCoordinates b degree) :=
  inferInstanceAs (Fintype {S : Finset (Fin b) // S.card ≤ degree})

def selectorEval {b degree : ℕ} (s : Fin b → Binary)
    (c : SelectorCoordinates b degree) : Binary := ∏ i ∈ c.val, s i

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

def interval (k : ℕ) (d : Tag k) : Finset (Tag k) :=
  Finset.univ.image (fun i : Fin k => d + (i.val + 1 : ℕ))

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

noncomputable instance (k n b degree : ℕ) : DecidableEq (Coordinate k n b degree) := Classical.decEq _

abbrev Vector (k n b degree : ℕ) := Coordinate k n b degree → Binary

abbrev Moment (k n b degree : ℕ) := Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary

def ordinary {k n : ℕ} (d t : Tag k) (i : Fin n) : Base k n := Sum.inl ((d, t), i)

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

def blockTester {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    Moment k n b degree →ₗ[Binary] Binary :=
  ∑ ρ : Fin r, matrixEntry (emptySelector b degree, some (c (pairLeft h ρ)))
    (emptySelector b degree, some (c (pairRight h ρ)))

def etaO {k n b degree r : ℕ} (h : 2 * r ≤ n) : Moment k n b degree →ₗ[Binary] Binary :=
  ∑ d : Tag k, ∑ t : Tag k, blockTester h (ordinary d t)

def blockForm {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ ρ : Fin r, GradientForm.rankOne
    (LinearMap.proj (emptySelector b degree, some (c (pairLeft h ρ))))
    (LinearMap.proj (emptySelector b degree, some (c (pairRight h ρ))))

def testerForm {k n b degree r : ℕ} (h : 2 * r ≤ n) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  (∑ d : Tag k, ∑ t : Tag k, blockForm h (ordinary d t)) + blockForm h shared

def sharpForm {k n b degree : ℕ} (h : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ a : Fin b, ∑ i : Fin n, ∑ j : Fin n, M a i j •
    (GradientForm.rankOne (LinearMap.proj (bitSelector h a, some (sharp i)))
      (LinearMap.proj (emptySelector b degree, some (sharp j))) +
    GradientForm.rankOne (LinearMap.proj (emptySelector b degree, some (sharp i)))
      (LinearMap.proj (bitSelector h a, some (sharp j))))

noncomputable def selfGram {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) : Moment k n b degree :=
  (testerForm hr + sharpForm hd M).toMatrix'

end Lax342547.ConcreteGeometry
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

-- Lax342547.GramNormalization
section
namespace Lax342547.GramNormalization
end Lax342547.GramNormalization
end

-- Lax342547.AffineSliceIndependence
section
namespace Lax342547.AffineSliceIndependence.affineColumns
end Lax342547.AffineSliceIndependence.affineColumns

namespace Lax342547.AffineSliceIndependence.eraseFree
end Lax342547.AffineSliceIndependence.eraseFree

namespace Lax342547.AffineSliceIndependence.joinedFree
end Lax342547.AffineSliceIndependence.joinedFree

namespace Lax342547.AffineSliceIndependence

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open scoped ENNReal

/-- Coefficients of the actual affine point map at a fixed selector. -/
def pointColumns {k n b degree : ℕ} {D : Type} (s : Fin b → Binary)
    (V : Matrix (Base k n) (Option D) Binary) : Matrix (Coordinate k n b degree) (Option D) Binary :=
  fun c j => selectorEval s c.1 * match c.2 with
    | none => match j with | none => 1 | some _ => 0
    | some a => V a j

end Lax342547.AffineSliceIndependence
end

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh
end Lax342547.Walsh
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh
end Lax342547.PushforwardWalsh
end

-- Lax342547.RetainedImages
section
namespace Lax342547.RetainedImages
end Lax342547.RetainedImages
end

-- Lax342547.RealCellLaws
section
namespace Lax342547.RealCellLaws
end Lax342547.RealCellLaws
end

-- Lax342547.ConditionedAffineColumns
section
namespace Lax342547.ConditionedAffineColumns
end Lax342547.ConditionedAffineColumns
end

-- Lax342547.RelativeEntropy
section
namespace Lax342547.RelativeEntropy
end Lax342547.RelativeEntropy
end

-- Lax342547.EntropyLines
section
namespace Lax342547.EntropyLines
end Lax342547.EntropyLines
end

-- Lax342547.EntropyProjection
section
namespace Lax342547.EntropyProjection
end Lax342547.EntropyProjection
end

-- Lax342547.PairRecovery
section
namespace Lax342547.PairRecovery
end Lax342547.PairRecovery
end

-- Lax342547.UnitLaws
section
namespace Lax342547.UnitLaws
end Lax342547.UnitLaws
end

-- Lax342547.ContainerLaws
section
namespace Lax342547.ContainerLaws
end Lax342547.ContainerLaws
end

-- Lax342547.FiniteSampling
section
namespace Lax342547.FiniteSampling
end Lax342547.FiniteSampling
end

-- Lax342547.EmpiricalVariance
section
namespace Lax342547.EmpiricalVariance
end Lax342547.EmpiricalVariance
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

-- Lax342547.FrameTuples
section
namespace Lax342547.FrameTuples
end Lax342547.FrameTuples
end

-- Lax342547.JoinedGramOrbits
section
namespace Lax342547.JoinedGramOrbits
end Lax342547.JoinedGramOrbits
end

-- Lax342547.FourierTests
section
namespace Lax342547.FourierTests
end Lax342547.FourierTests
end

-- Lax342547.ConditionedMixing
section
namespace Lax342547.ConditionedMixing
end Lax342547.ConditionedMixing
end

-- Lax342547.BilinearWalsh
section
namespace Lax342547.BilinearWalsh
end Lax342547.BilinearWalsh
end

-- Lax342547.SlotWalsh
section
namespace Lax342547.SlotWalsh
end Lax342547.SlotWalsh
end

-- Lax342547.CrossBatchMixing
section
namespace Lax342547.CrossBatchMixing
end Lax342547.CrossBatchMixing
end

-- Lax342547.CrossGramBasis
section
namespace Lax342547.CrossGramBasis
end Lax342547.CrossGramBasis

namespace Lax342547.CrossGramBasis.tests
end Lax342547.CrossGramBasis.tests
end

-- Lax342547.GramOrbitDensity
section
namespace Lax342547.GramOrbitDensity
end Lax342547.GramOrbitDensity

namespace Lax342547.GramOrbitDensity.batchEquiv
end Lax342547.GramOrbitDensity.batchEquiv
end

-- Lax342547.JointGramInjection
section
namespace Lax342547.JointGramInjection
end Lax342547.JointGramInjection

namespace Lax342547.JointGramInjection.ambientEquiv
end Lax342547.JointGramInjection.ambientEquiv
end

-- Lax342547.RawBatchComparison
section
namespace Lax342547.RawBatchComparison
end Lax342547.RawBatchComparison

namespace Lax342547.RawBatchComparison.target
end Lax342547.RawBatchComparison.target
end

-- Lax342547.RawFrameComparison
section
namespace Lax342547.RawFrameComparison
end Lax342547.RawFrameComparison
end

-- Lax342547.GroupTensorComparison
section
namespace Lax342547.GroupTensorComparison
end Lax342547.GroupTensorComparison
end

-- Lax342547.RawGroupedComparison
section
namespace Lax342547.RawGroupedComparison
end Lax342547.RawGroupedComparison
end

-- Lax342547.AffineSliceVariance
section
namespace Lax342547.AffineSliceVariance
end Lax342547.AffineSliceVariance
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
namespace Lax342547.Atoms.testerSummary
end Lax342547.Atoms.testerSummary

namespace Lax342547.Atoms

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.ConcreteCut

inductive Flavor (k : ℕ) where
  | generic
  | sharedOnly
  | pure (blocks : Finset (Tag k × Tag k))
  deriving Fintype

def retained {k n : ℕ} (l : Tag k) (f : Flavor k) : Set (Base k n)
  | Sum.inl ((d, t), _) => l ∈ interval k d ∧ match f with
      | .generic => True
      | .sharedOnly => False
      | .pure blocks => (d, t) ∈ blocks
  | Sum.inr (q, _) => match f with
      | .pure _ => q ≠ 0
      | _ => True

abbrev Parameters {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) :=
  {i : Base k n // i ∈ retained l f} → Binary

noncomputable def parameterValue {k n : ℕ} {l : Tag k} {f : Flavor k} (p : Parameters n l f)
    (i : Base k n) : Binary := by
  classical
  exact if hi : i ∈ retained l f then p ⟨i, hi⟩ else 0

end Lax342547.Atoms
end

-- Lax342547.FlavorAffineSlices
section
namespace Lax342547.FlavorAffineSlices

noncomputable section

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.AffineSliceIndependence Lax342547.RetainedImages Lax342547.RealCellLaws

open Lax342547.RawFrames Lax342547.FrameTuples Lax342547.GramOrbitDensity Lax342547.RelativeEntropy

open Lax342547.AffineSliceVariance

open scoped BigOperators ENNReal

abbrev Coefficients {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) (D : Type) :=
    Matrix {i : Base k n // i ∈ retained (k := k) (n := n) l f} (Option D) Binary

noncomputable def value {k n : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    (V : Coefficients n l f D) : Matrix (Base k n) (Option D) Binary :=
    fun i j => parameterValue (fun a => V a j) i

end

end Lax342547.FlavorAffineSlices
end

-- Lax342547.FixedSelectorGram
section
namespace Lax342547.FixedSelectorGram

noncomputable section

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.AffineSliceIndependence Lax342547.FlavorAffineSlices Lax342547.Atoms

open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

abbrev TesterBlock (k : ℕ) := Option (Tag k × Tag k)

def testerCoordinate {k n r : ℕ} (hr : 2*r ≤ n)
    (u : TesterBlock k × Fin r × Bool) : Base k n :=
  let i := if u.2.2 then pairRight hr u.2.1 else pairLeft hr u.2.1
  match u.1 with
  | none => shared i
  | some (d,t) => ordinary d t i

def blockRetained {k : ℕ} (l : Tag k) (f : Flavor k) : TesterBlock k → Prop
  | none => match f with | .pure _ => False | _ => True
  | some (d,t) => l ∈ interval k d ∧ match f with
      | .generic => True | .sharedOnly => False | .pure blocks => (d,t) ∈ blocks

abbrev Slots {k : ℕ} (l : Tag k) (f : Flavor k) (r : ℕ) :=
  {q : TesterBlock k // blockRetained l f q} × Fin r × Bool

noncomputable instance {k : ℕ} (l : Tag k) (f : Flavor k) :
    Fintype {q : TesterBlock k // blockRetained l f q} := Fintype.ofFinite _

def slotIndex {k n r : ℕ} (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k)
    (u : Slots l f r) : {a : Base k n // a ∈ retained l f} :=
  ⟨testerCoordinate hr (u.1.val,u.2), (show testerCoordinate hr (u.1.val,u.2) ∈ retained (n := n) l f ↔ blockRetained l f u.1.val from by
      change retained l f (testerCoordinate hr (u.1.val,u.2)) ↔ _
      cases u.1.val with
      | none => cases f <;> simp [testerCoordinate,shared,retained,blockRetained]
      | some q => cases f <;> simp [testerCoordinate,ordinary,retained,blockRetained]).mpr u.1.property⟩

def restrictTesters {k n r : ℕ} {D : Type} (hr : 2*r ≤ n) (l : Tag k) (f : Flavor k) :
    Coefficients n l f D →ₗ[Binary] Matrix (Slots l f r) (Option D) Binary where
  toFun V := fun u j => V (slotIndex hr l f u) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restrictedGram {k r : ℕ} {l : Tag k} {f : Flavor k} {D : Type}
    (X : Matrix (Slots l f r) (Option D) Binary) : Matrix (Option D) (Option D) Binary :=
  fun i j => ∑ q : {q : TesterBlock k // blockRetained l f q},∑ ρ : Fin r,
    X (q,ρ,false) i*X (q,ρ,true) j

axiom gram_restriction {k n b degree r : ℕ} {D : Type}
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k) (V : Coefficients n l f D) :
    (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) =
      restrictedGram (restrictTesters hr l f V)

end

end Lax342547.FixedSelectorGram
end
