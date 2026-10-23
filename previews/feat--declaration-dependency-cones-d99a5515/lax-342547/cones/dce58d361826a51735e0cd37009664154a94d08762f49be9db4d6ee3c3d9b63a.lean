-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

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

def momentSpace (p : Label → Coord → Binary) (A : Set Base) :
    Submodule Binary (Matrix (Coord × Option Base) (Coord × Option Base) Binary) :=
  Submodule.span Binary {w | ∃ s z, (∀ i, i ∉ A → z i = 0) ∧ w = pointMoment p s z}

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

noncomputable instance {E : Matrix B B Binary} : Fintype (Frame B H N E) :=
  by classical exact Fintype.ofInjective frameData frameData_injective

def sandwich (P Q : Matrix N B Binary) : Matrix B B Binary →ₗ[Binary] Matrix N N Binary where
  toFun Z := P * Z * Q.transpose
  map_add' Z W := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Z := by simp [Matrix.mul_smul, Matrix.smul_mul]

variable {Comp : Type}

def profileMap {E : Matrix B B Binary} (F : Comp → Frame B H N E) :
    (Comp → Matrix B B Binary) →ₗ[Binary] (Comp → Matrix N N Binary) where
  toFun x e := sandwich (F e).P (F e).Q (x e)
  map_add' x y := by ext e i j; simp
  map_smul' c x := by ext e i j; simp

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

-- Lax342547.KernelWitness
section
namespace Lax342547.KernelWitness
end Lax342547.KernelWitness
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

open Lax342547.MomentSpace

variable {X Tag : Type} [AddCommGroup X] [Module Binary X] [Fintype Tag]

def rankOne (a b : X →ₗ[Binary] Binary) : LinearMap.BilinForm Binary X := a.smulRight b

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

def eta {k n b degree r : ℕ} (h : 2 * r ≤ n) : Moment k n b degree →ₗ[Binary] Binary :=
  etaO h + blockTester h shared

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

-- Lax342547.TensorIntersections
section
namespace Lax342547.TensorIntersections

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ConcreteGeometry

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

def intersectionSpace (P Q : Matrix N B Binary) : Submodule Binary (N → Binary) :=
  LinearMap.range P.mulVecLin ⊓ LinearMap.range Q.mulVecLin

end Lax342547.TensorIntersections
end

-- Lax342547.RawIntersections
section
namespace Lax342547.RawIntersections

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

open Lax342547.ProductImages Lax342547.TensorIntersections

open scoped ENNReal

variable {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]

noncomputable def intersectionDimension {E : Matrix B B Binary}
    (o : Fin 2 → Comp → Frame B H N E) : ℕ :=
  ∑ e, Module.finrank Binary (intersectionSpace (o 0 e).P (o 1 e).P)

end Lax342547.RawIntersections
end

-- Lax342547.ConcreteCut
section
namespace Lax342547.ConcreteCut.Testers
end Lax342547.ConcreteCut.Testers

namespace Lax342547.ConcreteCut

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles

noncomputable instance (k : ℕ) : Fintype (Component (Tag k)) := by
  classical
  exact inferInstanceAs (Fintype {e : Finset (Tag k) // e.card = 2})

noncomputable instance (k : ℕ) : DecidableEq (Component (Tag k)) := Classical.decEq _

def tagSpace (k n b degree : ℕ) (l : Tag k) : Submodule Binary (Moment k n b degree) :=
  momentSpace selectorEval (allowedBase k n l)

abbrev Representation (k n b degree : ℕ) := representatives (tagSpace k n b degree)

def representationCut (k n b degree : ℕ) :
    Representation k n b degree →ₗ[Binary] (Component (Tag k) → Moment k n b degree) :=
  cutMap.comp (representatives (tagSpace k n b degree)).subtype

abbrev Profile (k n b degree : ℕ) := LinearMap.range (representationCut k n b degree)

def representativeAt {k n b degree : ℕ} (l : Tag k) :
    Representation k n b degree →ₗ[Binary] Moment k n b degree :=
  (LinearMap.proj l).comp (representatives (tagSpace k n b degree)).subtype

def ordinarySum {k n b degree r : ℕ} (hr : 2 * r ≤ n) (t : Tag k) :
    Representation k n b degree →ₗ[Binary] Binary :=
  ∑ l : Tag k, ∑ d : Tag k, (blockTester hr (ordinary d t)).comp (representativeAt l)

/-- Unlike a and b, this quantity belongs to a specified representation. -/
def chiStar {k n b degree r : ℕ} (hr : 2 * r ≤ n) :
    Representation k n b degree →ₗ[Binary] Binary :=
  ∑ l : Tag k, (eta hr).comp (representativeAt l)

end Lax342547.ConcreteCut
end

-- Lax342547.CutSparsity
section
namespace Lax342547.CutSparsity

open Lax342547.MomentSpace Lax342547.CutProfiles

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

noncomputable def valueCount (w : Tag → V) (c : V) : ℕ := Nat.card {t : Tag // w t = c}

noncomputable def supportSize (w : Tag → V) : ℕ := Nat.card {t : Tag // w t ≠ 0}

end Lax342547.CutSparsity
end

-- Lax342547.SparseRepresentatives
section
namespace Lax342547.SparseRepresentatives

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.CutSparsity Lax342547.ConcreteCut

open Lax342547.RawFrames Lax342547.TensorIntersections

def Normalized {k n b degree : ℕ} (x : Profile k n b degree)
    (w : Representation k n b degree) : Prop :=
  representationCut k n b degree w = x.val ∧
    2 * k + 1 < 2 * valueCount w.val 0

end Lax342547.SparseRepresentatives
end

-- Lax342547.SparseIntersections
section
namespace Lax342547.SparseIntersections

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.CutSparsity Lax342547.ConcreteCut

open Lax342547.RawFrames Lax342547.RawIntersections Lax342547.SparseRepresentatives

open scoped ENNReal

axiom raw_intersections {k n b degree r h N : ℕ}
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (D : ℕ) (hD : 1 ≤ D) (hsmall : 8 * D < (2 * k + 1) * (2 * k + 1))
    (hN : 2 * (Fintype.card (Coordinate k n b degree) + h) + 1 ≤ N)
    (hp : (4 : ℝ) * (Fintype.card (Coordinate k n b degree) + h : ℕ) ≤ (1 / 4 : ℝ) * N)
    (hc : (8 : ℝ) * Fintype.card (Component (Tag k)) ≤ (1 / 4 : ℝ) * N)
    (hcount : (Fintype.card (Component (Tag k)) * (2 * (Fintype.card (Coordinate k n b degree) + h)) * (2 * D) : ℕ) ≤
      (D : ℝ) * N / 4)
    (σ : PMF (Fin 2 → Component (Tag k) →
      Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)))
    (hσ : ∀ o, σ o ≤ (2 : ℝ≥0∞) ^ (D * N) / Fintype.card (Fin 2 → Component (Tag k) →
      Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M))) :
    σ.toOuterMeasure {o | 2 * D < intersectionDimension o} ≤ (2 : ℝ≥0∞) ^ (-((D : ℝ) * N / 4)) ∧
      ∀ o : Fin 2 → Component (Tag k) →
        Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M),
        intersectionDimension o ≤ 2 * D →
        ∀ x y : Profile k n b degree, profileMap (o 0) x.val = profileMap (o 1) y.val →
          (∑ e, (x.val e).rank) ≤ 2 * D ∧ (∑ e, (y.val e).rank) ≤ 2 * D ∧
          ∃ w v : Representation k n b degree, Normalized x w ∧ Normalized y v ∧
            supportSize w.val ≤ 4 * D / (2 * k + 1) ∧ supportSize v.val ≤ 4 * D / (2 * k + 1) ∧
            chiStar hr w = chiStar hr v ∧
            (∀ u : Representation k n b degree, Normalized x u → u = w) ∧
            (∀ u : Representation k n b degree, Normalized y u → u = v)

end Lax342547.SparseIntersections
end
