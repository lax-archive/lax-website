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

variable [Fintype N] {ΩA ΩB : Type}

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
end Lax342547.GradientRealization
end

-- Lax342547.FourHoles
section
namespace Lax342547.FourHoles
end Lax342547.FourHoles
end

-- Lax342547.PrimalRecords
section
namespace Lax342547.PrimalRecords

open Lax342547.MomentSpace Lax342547.TableContractions Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.TagGeometry Lax342547.CutProfiles

open Lax342547.PairedWitnesses Lax342547.RawContractions Lax342547.RawFrames Lax342547.HoleRelation

def Agreement {Comp B H : Type} [Fintype H] (F G : CrossForms Comp B H) : Prop :=
  (∀ e i z, fullPlus F e i z = fullPlus G e i z ∧ fullMinus F e i z = fullMinus G e i z) ∧
  (∀ e i z, fullPlus F.flip e i z = fullPlus G.flip e i z ∧ fullMinus F.flip e i z = fullMinus G.flip e i z)

axiom agreement_contractions {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (F G : CrossForms Comp B H) (h : Agreement F G)
    (X : Submodule Binary (Comp → Matrix B B Binary)) :
    (∀ i z, fullContraction F X i z = fullContraction G X i z) ∧
    (∀ i z, fullContraction F.flip X i z = fullContraction G.flip X i z)

end Lax342547.PrimalRecords
end
