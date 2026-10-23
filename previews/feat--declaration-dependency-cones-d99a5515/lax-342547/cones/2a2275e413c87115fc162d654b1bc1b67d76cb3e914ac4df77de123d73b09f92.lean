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

def momentSpace (p : Label → Coord → Binary) (A : Set Base) :
    Submodule Binary (Matrix (Coord × Option Base) (Coord × Option Base) Binary) :=
  Submodule.span Binary {w | ∃ s z, (∀ i, i ∉ A → z i = 0) ∧ w = pointMoment p s z}

end Lax342547.MomentSpace
end

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm

open Lax342547.MomentSpace

variable {X Tag : Type} [AddCommGroup X] [Module Binary X] [Fintype Tag]

def rankOne (a b : X →ₗ[Binary] Binary) : LinearMap.BilinForm Binary X := a.smulRight b

def form (a : X →ₗ[Binary] Binary) (aTag bTag : Tag → X →ₗ[Binary] Binary)
    (B : LinearMap.BilinForm Binary X) : LinearMap.BilinForm Binary X :=
  rankOne a a + (∑ t, (rankOne (aTag t) (bTag t) + rankOne (bTag t) (aTag t))) + B + B.flip

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

def sandwich (P Q : Matrix N B Binary) : Matrix B B Binary →ₗ[Binary] Matrix N N Binary where
  toFun Z := P * Z * Q.transpose
  map_add' Z W := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Z := by simp [Matrix.mul_smul, Matrix.smul_mul]

def contraction {E : Matrix B B Binary} (F : Frame B H N E) :
    Matrix N N Binary →ₗ[Binary] Binary where
  toFun Z := Matrix.trace (F.X * F.Y.transpose * Z)
  map_add' Z W := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c Z := by simp [Matrix.mul_smul, Matrix.trace_smul]

variable {Comp : Type}

def profileMap {E : Matrix B B Binary} (F : Comp → Frame B H N E) :
    (Comp → Matrix B B Binary) →ₗ[Binary] (Comp → Matrix N N Binary) where
  toFun x e := sandwich (F e).P (F e).Q (x e)
  map_add' x y := by ext e i j; simp
  map_smul' c x := by ext e i j; simp

def profileContraction [Fintype Comp] {E : Matrix B B Binary} (F : Comp → Frame B H N E) :
    (Comp → Matrix N N Binary) →ₗ[Binary] Binary :=
  ∑ e, (contraction (F e)).comp (LinearMap.proj e)

end Lax342547.RawFrames
end

-- Lax342547.ConcreteCut
section
namespace Lax342547.ConcreteCut

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles

noncomputable instance (k : ℕ) : Fintype (Component (Tag k)) := by
  classical
  exact inferInstanceAs (Fintype {e : Finset (Tag k) // e.card = 2})

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

noncomputable def sharedSum {k n b degree r : ℕ} (hr : 2 * r ≤ n) (t : Tag k) :
    Representation k n b degree →ₗ[Binary] Binary := by
  classical
  exact ∑ l ∈ Finset.univ.erase t, (blockTester hr shared).comp (representativeAt l)

structure Testers {k n b degree r : ℕ} (hr : 2 * r ≤ n) where
  aTag : Tag k → Profile k n b degree →ₗ[Binary] Binary
  bTag : Tag k → Profile k n b degree →ₗ[Binary] Binary
  ordinary_formula : ∀ t w, aTag t ((representationCut k n b degree).rangeRestrict w) = ordinarySum hr t w
  shared_formula : ∀ t w, bTag t ((representationCut k n b degree).rangeRestrict w) = sharedSum hr t w

def Testers.role {k n b degree r : ℕ} {hr : 2 * r ≤ n} (D : Testers (k := k) (b := b) (degree := degree) hr) :
    Profile k n b degree →ₗ[Binary] Binary := ∑ t, D.aTag t

def profileAt {k n b degree : ℕ} (e : Component (Tag k)) :
    Profile k n b degree →ₗ[Binary] Moment k n b degree :=
  (LinearMap.proj e).comp (LinearMap.range (representationCut k n b degree)).subtype

def matrixPairing {I : Type} [Fintype I] : LinearMap.BilinForm Binary (Matrix I I Binary) where
  toFun := matrixPair
  map_add' x y := by
    ext w
    simp [matrixPair, Matrix.add_apply, add_smul, Finset.sum_add_distrib, LinearMap.sum_apply]
  map_smul' a x := by
    ext w
    simp [matrixPair, Matrix.smul_apply, mul_smul, Finset.smul_sum, LinearMap.sum_apply]

noncomputable def mixingForm {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) :
    LinearMap.BilinForm Binary (Profile k n b degree) :=
  ∑ j, ∑ e, ∑ f, matrixPairing.comp (profileAt e)
    ((RawFrames.sandwich (L j e f) (R j e f)).comp (profileAt f))

noncomputable def gradient {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) :
    LinearMap.BilinForm Binary (Profile k n b degree) :=
  GradientForm.form D.role D.aTag D.bTag (mixingForm L R)

end Lax342547.ConcreteCut
end

-- Lax342547.SelectorInterpolation
section
namespace Lax342547.SelectorInterpolation
end Lax342547.SelectorInterpolation
end

-- Lax342547.SparsePins
section
namespace Lax342547.SparsePins

open Lax342547.MomentSpace

variable {Label Coord Base : Type}

def labelTensor (p : Label → Coord → Binary) (s : Label) :
    (Base → Binary) →ₗ[Binary] (Coord × Base → Binary) where
  toFun z i := p s i.1 * z i.2
  map_add' z w := by ext i; exact mul_add _ _ _
  map_smul' a z := by ext i; exact mul_left_comm _ _ _

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

def tensorSpace {B : Type} (S T : Submodule Binary (B → Binary)) :
    Submodule Binary (Matrix B B Binary) :=
  Submodule.span Binary {M | ∃ v ∈ S, ∃ w ∈ T, M = Matrix.vecMulVec v w}

def effective {Comp B H N : Type} (X : Submodule Binary (Comp → Matrix B B Binary))
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) : Submodule Binary X where
  carrier := {x | ∀ e, x.val e ∈ tensorSpace (projected P i (e, true)) (projected P i (e, false))}
  zero_mem' := fun _e => (tensorSpace _ _).zero_mem
  add_mem' := fun hx hy e => (tensorSpace _ _).add_mem (hx e) (hy e)
  smul_mem' := fun c _ hx e => (tensorSpace _ _).smul_mem c (hx e)

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

def tableSpace {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary) where
  carrier := {v | ∀ i, primalProjection i v ∈ projected P i a}
  zero_mem' := fun i => (projected P i a).zero_mem
  add_mem' := fun hv hw i => (projected P i a).add_mem (hv i) (hw i)
  smul_mem' := fun c _ hv i => (projected P i a).smul_mem c (hv i)

def pinnedPrimal {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (a : Comp × Bool) :
    Submodule Binary (B → Binary) := (P.space a).comap (primalEmbedding i)

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

end Lax342547.Atoms
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

noncomputable def PointAtom.profile {k n b degree : ℕ} (x : PointAtom k n b degree) :
    Profile k n b degree := atom x.tag x.label x.base x.supported

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

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.WitnessAtoms

def RecipeGradients {I J : Type} [Fintype I] [Fintype J]
    {k n b degree r copies : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (atoms : I ⊕ J → PointAtom k n b degree) (p : I ⊕ J → Binary) : Prop :=
  (∀ i : I, D.role (atoms (.inl i)).profile +
    gradient D L R (∑ t : I, (atoms (.inl t)).profile) (atoms (.inl i)).profile = 0) ∧
  (∀ j : J, D.role (atoms (.inr j)).profile +
    gradient D L R (∑ t : I, (atoms (.inl t)).profile) (atoms (.inr j)).profile = p (.inr j)) ∧
  (∀ j : J, D.role (atoms (.inr j)).profile +
    gradient D L R (∑ t : J, (atoms (.inr t)).profile) (atoms (.inr j)).profile = 0) ∧
  (∀ i : I, D.role (atoms (.inl i)).profile +
    gradient D L R (∑ t : J, (atoms (.inr t)).profile) (atoms (.inl i)).profile = p (.inl i))

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

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

variable {Comp B H N : Type}

structure Table (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) where
  forward : ∀ e, tableSpace P (e, true) →ₗ[Binary] tableSpace Q (e, false) →ₗ[Binary] Binary
  reverse : ∀ e, tableSpace Q (e, true) →ₗ[Binary] tableSpace P (e, false) →ₗ[Binary] Binary

def tableChannel (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) (i : Fin 2) :
    (H → Binary) →ₗ[Binary] tableSpace P a where
  toFun v := ⟨channelEmbedding i v, by
    intro j
    have hz : primalProjection j (channelEmbedding (B := B) i v) = 0 := by
      ext b
      simp [primalProjection, channelEmbedding]
    rw [hz]
    exact (projected P j a).zero_mem⟩
  map_add' v w := Subtype.ext ((channelEmbedding i).map_add v w)
  map_smul' c v := Subtype.ext ((channelEmbedding i).map_smul c v)

def tablePinnedPrimal (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a : Comp × Bool) (i : Fin 2) : pinnedPrimal P i a →ₗ[Binary] tableSpace P a where
  toFun v := ⟨primalEmbedding i v.val, fun _j => ⟨primalEmbedding i v.val, v.property, rfl⟩⟩
  map_add' v w := Subtype.ext ((primalEmbedding i).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((primalEmbedding i).map_smul c v.val)

noncomputable def rowChannels (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a b : Comp × Bool)
    (T : tableSpace P a →ₗ[Binary] tableSpace Q b →ₗ[Binary] Binary) (i z : Fin 2) :
    pinnedPrimal P i a →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun d h => T (tablePinnedPrimal P a i d) (tableChannel Q b z (Pi.single h 1))
      map_add' := by intro d d'; ext h; simp
      map_smul' := by intro c d; ext h; simp }

noncomputable def columnChannels (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a b : Comp × Bool)
    (T : tableSpace P a →ₗ[Binary] tableSpace Q b →ₗ[Binary] Binary) (z i : Fin 2) :
    pinnedPrimal Q i b →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun d h => T (tableChannel P a z (Pi.single h 1)) (tablePinnedPrimal Q b i d)
      map_add' := by intro d d'; ext h; simp
      map_smul' := by intro c d; ext h; simp }

def Injecting {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q) : Prop :=
  ∀ e i z,
    Function.Injective (((protectedChannel Q z (e, true)).mkQ).comp
      (rowChannels P Q (e, true) (e, false) (T.forward e) i z)) ∧
    Function.Injective (((protectedChannel Q z (e, false)).mkQ).comp
      (columnChannels Q P (e, true) (e, false) (T.reverse e) z i)) ∧
    Function.Injective (((protectedChannel P z (e, true)).mkQ).comp
      (rowChannels Q P (e, true) (e, false) (T.reverse e) i z)) ∧
    Function.Injective (((protectedChannel P z (e, false)).mkQ).comp
      (columnChannels P Q (e, true) (e, false) (T.forward e) z i))

variable [Fintype N] {ΩA ΩB : Type}

def Admissible {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (A : ΩA → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary))
    (Bmap : ΩB → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary))
    (oA : ΩA) (oB : ΩB) : Prop :=
  (∀ e (v : tableSpace P (e, true)) (w : tableSpace Q (e, false)),
    v.val ∈ P.space (e, true) ∨ w.val ∈ Q.space (e, false) →
    T.forward e v w = dotProduct (A oA (e, true) v.val) (Bmap oB (e, false) w.val)) ∧
  (∀ e (v : tableSpace Q (e, true)) (w : tableSpace P (e, false)),
    v.val ∈ Q.space (e, true) ∨ w.val ∈ P.space (e, false) →
    T.reverse e v w = dotProduct (Bmap oB (e, true) v.val) (A oA (e, false) w.val))

end Lax342547.SmallTables
end

-- Lax342547.TensorContractions
section
namespace Lax342547.TensorContractions

open Lax342547.MomentSpace Lax342547.ProjectedPins Lax342547.ConcreteGeometry

variable {B H : Type} [Fintype B] [Fintype H]

noncomputable def ambient (f g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Matrix B B Binary →ₗ[Binary] Binary := by
  classical
  exact matrixPair (LinearMap.BilinForm.toMatrix' ((dotProductBilin Binary Binary).compl₁₂ f g))

noncomputable def extend {S : Submodule Binary (B → Binary)} (f : S →ₗ[Binary] (H → Binary)) :
    (B → Binary) →ₗ[Binary] (H → Binary) := Classical.choose f.exists_extend

noncomputable def contraction {S T : Submodule Binary (B → Binary)}
    (f : S →ₗ[Binary] (H → Binary)) (g : T →ₗ[Binary] (H → Binary)) :
    tensorSpace S T →ₗ[Binary] Binary :=
  (ambient (extend f) (extend g)).comp (tensorSpace S T).subtype

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

def CrossForms.flip {Comp B H : Type} (F : CrossForms Comp B H) : CrossForms Comp B H :=
  ⟨F.reverse, F.forward⟩

def flipTable {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) : Table Q P := ⟨T.reverse, T.forward⟩

def Extends {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (F : CrossForms Comp B H) (T : Table P Q) : Prop :=
  (∀ e (v : tableSpace P (e, true)) (w : tableSpace Q (e, false)),
    F.forward e v.val w.val = T.forward e v w) ∧
  (∀ e (v : tableSpace Q (e, true)) (w : tableSpace P (e, false)),
    F.reverse e v.val w.val = T.reverse e v w)

def primalToTable {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) (i : Fin 2) :
    projected P i a →ₗ[Binary] tableSpace P a where
  toFun v := ⟨primalEmbedding i v.val, by
    intro j
    by_cases hji : j = i
    · subst j
      simp [primalProjection, primalEmbedding]
    · have hz : primalProjection j (primalEmbedding (H := H) i v.val) = 0 := by
        ext b
        simp [primalProjection, primalEmbedding, hji]
      rw [hz]
      exact (projected P j a).zero_mem⟩
  map_add' v w := Subtype.ext ((primalEmbedding i).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((primalEmbedding i).map_smul c v.val)

noncomputable def plus {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (e : Comp) (i z : Fin 2) : projected P i (e, true) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => T.forward e (primalToTable P (e, true) i v)
        (tableChannel Q (e, false) z (Pi.single h 1))
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

noncomputable def minus {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (e : Comp) (i z : Fin 2) : projected P i (e, false) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => T.reverse e (tableChannel Q (e, true) z (Pi.single h 1))
        (primalToTable P (e, false) i v)
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

noncomputable def fullPlus {Comp B H : Type} (F : CrossForms Comp B H) (e : Comp) (i z : Fin 2) :
    (B → Binary) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => F.forward e (primalEmbedding i v) (channelEmbedding z (Pi.single h 1))
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

noncomputable def fullMinus {Comp B H : Type} (F : CrossForms Comp B H) (e : Comp) (i z : Fin 2) :
    (B → Binary) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => F.reverse e (channelEmbedding z (Pi.single h 1)) (primalEmbedding i v)
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

def component {Comp B H N : Type} (X : Submodule Binary (Comp → Matrix B B Binary))
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (e : Comp) :
    effective X P i →ₗ[Binary] tensorSpace (projected P i (e, true)) (projected P i (e, false)) where
  toFun x := ⟨x.val.val e, x.property e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def starContraction {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) :
    effective X P i →ₗ[Binary] Binary :=
  ∑ e, (TensorContractions.contraction (plus T e i z) (minus T e i z)).comp (component X P i e)

noncomputable def fullContraction {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) :
    X →ₗ[Binary] Binary :=
  ∑ e, (TensorContractions.ambient (fullPlus F e i z) (fullMinus F e i z)).comp
    ((LinearMap.proj e).comp X.subtype)

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

def other (i : Fin 2) : Fin 2 := ⟨1 - i.val, by omega⟩

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}

noncomputable def leftWitness (W : Lists k n b degree r hr) (i z : Fin 2) : Profile k n b degree :=
  ∑ t, (W.left i z t).profile

noncomputable def rightWitness (W : Lists k n b degree r hr) (i z : Fin 2) : Profile k n b degree :=
  ∑ t, (W.right i z t).profile

def FreshAgainst (W : Lists k n b degree r hr) (A B : Fin 2 → Finset (Fin b → Binary)) : Prop :=
  (∀ i z t, (W.left i z t).label ∉ A i) ∧ (∀ i z t, (W.right i z t).label ∉ B z)

variable {H N : Type} [Fintype H] [Fintype N]
  {E : Moment k n b degree}

abbrev Unit := Fin 2 → Component (Tag k) → Frame (Coordinate k n b degree) H N E

noncomputable def ownContraction (o : Unit (H := H) (N := N) (E := E)) (i : Fin 2) :
    Profile k n b degree →ₗ[Binary] Binary :=
  (profileContraction (o (other i))).comp ((profileMap (o i)).comp (Profile k n b degree).subtype)

def MatchedKeys (W : Lists k n b degree r hr) (oA oB : Unit (H := H) (N := N) (E := E)) : Prop :=
  ∀ i z t (e : Component (Tag k)), (W.left i z t).tag ∈ e.val →
    (oA i e).P.mulVec (W.left i z t).vector = (oB z e).P.mulVec (W.right i z t).vector ∧
    (oA i e).Q.mulVec (W.left i z t).vector = (oB z e).Q.mulVec (W.right i z t).vector

structure ScalarRecipe (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    {P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N}
    (T : Table P Q) (A B : Fin 2 → Finset (Fin b → Binary)) : Prop where
  fresh : FreshAgainst W A B
  odd : ∀ i z, (∑ t, diagonalBit hr (W.left i z t)) = 1
  roles : ∀ i z, D.role (leftWitness W i z) + D.role (rightWitness W i z) = 1
  effectiveLeft : ∀ i z (x : effective (Profile k n b degree) P i),
    gradient D L R (leftWitness W i z) x.val = D.role x.val +
      starContraction T (Profile k n b degree) i z x
  effectiveRight : ∀ i z (x : effective (Profile k n b degree) Q z),
    gradient D L R (rightWitness W i z) x.val = D.role x.val +
      starContraction (flipTable T) (Profile k n b degree) z i x
  coupledLeft : ∀ i z,
    (ownContraction oA i + D.role) (leftWitness W i z) =
      (ownContraction oA (other i) + D.role) (leftWitness W (other i) z)
  coupledRight : ∀ i z,
    (ownContraction oB z + D.role) (rightWitness W i z) =
      (ownContraction oB (other z) + D.role) (rightWitness W i (other z))

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

abbrev Position (W : Lists k n b degree r hr) (i : Fin 2) :=
  Fin (W.length i 0) ⊕ Fin (W.length i 1)

def endpointAtoms (W : Lists k n b degree r hr) (i : Fin 2) :
    Position W i → PointAtom k n b degree := Sum.elim (W.left i 0) (W.left i 1)

variable {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

noncomputable def oppositeP (W : Lists k n b degree r hr)
    (oB : Unit (H := H) (N := N) (E := E)) (i : Fin 2) : Position W i → Binary :=
  Sum.elim (fun t => ownContraction oB 0 (W.right i 0 t).profile)
    (fun t => ownContraction oB 1 (W.right i 1 t).profile)

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

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins

open Lax342547.SparsePins Lax342547.KeySpans

variable {Base Comp H N : Type} {b degree : ℕ}

def Covers
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (R : ℕ) : Prop :=
  ∀ i a (L : Finset (Fin b → Binary)) (v : (Fin b → Binary) → Option Base → Binary),
    L.card ≤ R + 14 →
    (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) ∈ projected P i a →
    ∀ s ∈ L, v s ≠ 0 → s ∈ A i

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

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses

open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PairedAnnihilators

open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions

open Lax342547.DerivativeResponses Lax342547.ResponseMatrices Lax342547.RawBaselines

open Lax342547.TableSpaces Lax342547.BaseCompression Lax342547.QuotientCompression

open Lax342547.ResidualRealization

noncomputable def blockBound (k b degree K R : ℕ) : ℕ :=
  2 * Fintype.card (SelectorCoordinates b degree) * Fintype.card (Component (Tag k)) * (K + 14 + R)

noncomputable def quotientBound (k b degree K R : ℕ) : ℕ :=
  2 * Fintype.card (SelectorCoordinates b degree) *
    (1 + ((2 * k + 1)^2 + 3) * blockBound k b degree K R) + 2 * K

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
end Lax342547.FrozenAssembly
end

-- Lax342547.FrozenGradients
section
namespace Lax342547.FrozenGradients
end Lax342547.FrozenGradients
end

-- Lax342547.GradientRealization
section
namespace Lax342547.GradientRealization

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses

open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PairedAnnihilators

open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions

open Lax342547.DerivativeResponses Lax342547.ResponseMatrices Lax342547.RawBaselines

open Lax342547.TableSpaces Lax342547.BaseCompression Lax342547.QuotientCompression

open Lax342547.ResidualRealization

open Lax342547.CompressedResidual

axiom gradient_realization {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] [Fintype N] {K : ℕ} {E : Moment k n b degree}
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (hQ : Q.rank ≤ K) (A B : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (hB : Lax342547.PinLabelExclusions.Covers Q B (2 * K + 28))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (hrecipe : ScalarRecipe W D L R oA oB T A B) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients D L R
      (Lax342547.PairedRecipes.endpointAtoms W i) (Lax342547.PairedRecipes.oppositeP W oB i))
    (hgradients' : ∀ z, Lax342547.ConcreteRecipes.RecipeGradients D L R
      (Lax342547.PairedRecipes.endpointAtoms (Lax342547.PairedRecipes.flip W) z)
      (Lax342547.PairedRecipes.oppositeP (Lax342547.PairedRecipes.flip W) oA z))
    (hadmissible : Lax342547.SmallTables.Admissible T Lax342547.ReferencePins.observation
      Lax342547.ReferencePins.observation oA oB)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree)
    (hmargin : 28 * copies * Fintype.card (Component (Tag k)) +
      quotientBound k b degree K (14 * K + 140) + 2 * K + 4 * (3 * K + 28) < 970 * r)
    (hchannels : 1000 * r ≤ Fintype.card H) :
    ∃ G : CrossForms (Component (Tag k)) (Coordinate k n b degree) H,
      Frozen G W P Q oA oB ∧
      (∀ i z x, fullContraction G (Profile k n b degree) i z x =
        (D.role + gradient D L R (leftWitness W i z)) x) ∧
      (∀ i z x, fullContraction G.flip (Profile k n b degree) z i x =
        (D.role + gradient D L R (rightWitness W i z)) x)

end Lax342547.GradientRealization
end
