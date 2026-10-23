-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
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
namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

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

def momentSpace (p : Label → Coord → Binary) (A : Set Base) :
    Submodule Binary (Matrix (Coord × Option Base) (Coord × Option Base) Binary) :=
  Submodule.span Binary {w | ∃ s z, (∀ i, i ∉ A → z i = 0) ∧ w = pointMoment p s z}

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

def cutMap : (Tag → V) →ₗ[Binary] (Component Tag → V) where
  toFun w e := ∑ t ∈ e.val, w t
  map_add' w v := by ext e; simp [Finset.sum_add_distrib]
  map_smul' c w := by ext e; simp [Finset.smul_sum]

def representatives (W : Tag → Submodule Binary V) : Submodule Binary (Tag → V) :=
  Submodule.pi Set.univ W

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
end Lax342547.RawFrames

namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame
end

-- Lax342547.ConcreteCut
section
namespace Lax342547.ConcreteCut.Testers
end Lax342547.ConcreteCut.Testers

namespace Lax342547.ConcreteCut

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles

def tagSpace (k n b degree : ℕ) (l : Tag k) : Submodule Binary (Moment k n b degree) :=
  momentSpace selectorEval (allowedBase k n l)

abbrev Representation (k n b degree : ℕ) := representatives (tagSpace k n b degree)

def representationCut (k n b degree : ℕ) :
    Representation k n b degree →ₗ[Binary] (Component (Tag k) → Moment k n b degree) :=
  cutMap.comp (representatives (tagSpace k n b degree)).subtype

abbrev Profile (k n b degree : ℕ) := LinearMap.range (representationCut k n b degree)

end Lax342547.ConcreteCut
end

-- Lax342547.Atoms
section
namespace Lax342547.Atoms.testerSummary
end Lax342547.Atoms.testerSummary

namespace Lax342547.Atoms

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.ConcreteCut

noncomputable def atomRepresentation {k n b degree : ℕ} (l : Tag k)
    (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) : Representation k n b degree := by
  classical
  refine ⟨Pi.single l (pointMoment selectorEval s z), ?_⟩
  intro t _
  by_cases ht : l = t
  · subst t
    simp only [Pi.single_eq_same]
    exact Submodule.subset_span ⟨s, z, hz, rfl⟩
  · simp [ht]

noncomputable def atom {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) : Profile k n b degree :=
  (representationCut k n b degree).rangeRestrict (atomRepresentation l s z hz)

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

noncomputable instance {k n : ℕ} (l : Tag k) (f : Flavor k) :
    Fintype {i : Base k n // i ∈ retained l f} := Fintype.ofFinite _

end Lax342547.Atoms
end

-- Lax342547.CommonAtoms
section
namespace Lax342547.CommonAtoms
end Lax342547.CommonAtoms
end

-- Lax342547.BaseMoments
section
namespace Lax342547.BaseMoments
end Lax342547.BaseMoments
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

open Lax342547.PushforwardWalsh

noncomputable def cellMass {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if C ω then ρ ω else 0

end Lax342547.RetainedImages
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

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.RealCellLaws
section
namespace Lax342547.RealCellLaws
end Lax342547.RealCellLaws
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

-- Lax342547.SelectorInterpolation
section
namespace Lax342547.SelectorInterpolation
end Lax342547.SelectorInterpolation
end

-- Lax342547.BooleanWeight
section
namespace Lax342547.BooleanWeight
end Lax342547.BooleanWeight
end

-- Lax342547.QuadraticDegree
section
namespace Lax342547.QuadraticDegree
end Lax342547.QuadraticDegree
end

-- Lax342547.PointQuadratics
section
namespace Lax342547.PointQuadratics
end Lax342547.PointQuadratics
end

-- Lax342547.AtomFunctionals
section
namespace Lax342547.AtomFunctionals
end Lax342547.AtomFunctionals
end

-- Lax342547.PolynomialTensors
section
namespace Lax342547.PolynomialTensors
end Lax342547.PolynomialTensors
end

-- Lax342547.AtomParameters
section
namespace Lax342547.AtomParameters

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut

open Lax342547.ConcreteGeometry Lax342547.SelectorInterpolation

noncomputable def ParameterSize {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) :=
  Fintype.card {i : Base k n // i ∈ retained l f}

noncomputable def parameterBase {k n : ℕ} (l : Tag k) (f : Flavor k)
    (x : Fin (ParameterSize n l f) → Binary) (i : Base k n) : Binary := by
  classical
  exact if hi : i ∈ retained l f then x ((Fintype.equivFin _).toFun ⟨i,hi⟩) else 0

noncomputable def parameterAtom {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (f : Flavor k)
    (x : Fin (ParameterSize n l f) → Binary) : Profile k n b degree :=
  atom l s (parameterBase l f x) (by
    classical
    intro i hi
    have hn : i ∉ retained l f := by
      rintro hf
      apply hi
      cases i with
      | inl j => exact hf.1
      | inr j => trivial
    simp [parameterBase,hn])

end Lax342547.AtomParameters
end

-- Lax342547.SharedTesterPoint
section
namespace Lax342547.SharedTesterPoint
end Lax342547.SharedTesterPoint

namespace Lax342547.SharedTesterPoint.sharedTesterPoint
end Lax342547.SharedTesterPoint.sharedTesterPoint
end

-- Lax342547.EmptyPredictions
section
namespace Lax342547.EmptyPredictions
end Lax342547.EmptyPredictions
end

-- Lax342547.FiniteMoments
section
namespace Lax342547.FiniteMoments
end Lax342547.FiniteMoments
end

-- Lax342547.MomentTails
section
namespace Lax342547.MomentTails
end Lax342547.MomentTails
end

-- Lax342547.RetainedEmptyPredictions
section
namespace Lax342547.RetainedEmptyPredictions

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut

open Lax342547.ConcreteGeometry Lax342547.RetainedImages Lax342547.RelativeEntropy

open Lax342547.AtomParameters

open scoped BigOperators

noncomputable def predictionError {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary) (l : Tag k) (s : Fin b → Binary) : ℝ :=
  cellMass (fun _ : Fin (ParameterSize n l Flavor.generic) → Binary =>
    1/(2 : ℝ)^(ParameterSize n l Flavor.generic))
    (fun x => φ (parameterAtom (degree := degree) l s Flavor.generic x)+
      γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s (parameterBase l Flavor.generic x)) ≠ 0)

noncomputable def totalPredictionError {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary) (E : Finset (Fin b → Binary)) : ℝ := by
  classical
  exact ∑ l : Tag k,∑ s : Fin b → Binary,if s ∈ E then 0 else predictionError hr φ γ l s

axiom prediction_error_le_total {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary) (E : Finset (Fin b → Binary))
    (l : Tag k) (s : Fin b → Binary) (hs : s ∉ E) :
    predictionError hr φ γ l s ≤ totalPredictionError hr φ γ E

end Lax342547.RetainedEmptyPredictions
end
