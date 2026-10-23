-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi

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

open Lax342547.MomentSpace Lax342547.SparsePins Lax342547.ConcreteGeometry

open Lax342547.TensorAnnihilators

def block {Label Coord Base : Type} (p : Label → Coord → Binary) (s : Label) :
    Matrix Base Base Binary →ₗ[Binary] Matrix (Coord × Base) (Coord × Base) Binary where
  toFun Z i j := p s i.1 * p s j.1 * Z i.2 j.2
  map_add' Z W := by ext i j; exact mul_add _ _ _
  map_smul' c Z := by
    ext i j
    change p s i.1 * p s j.1 * (c * Z i.2 j.2) = c * (p s i.1 * p s j.1 * Z i.2 j.2)
    ring

axiom quotient_isolation {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    [DecidableEq Label]
    (p : Label → Coord → Binary) (L : Finset Label) (s : Label) (hs : s ∈ L)
    (Z : Label → Matrix Base Base Binary)
    (S T : Submodule Binary (Coord × Base → Binary))
    (A B : Submodule Binary (Base → Binary))
    (q : ((Coord × Base → Binary) ⧸ S) →ₗ[Binary] ((Base → Binary) ⧸ A))
    (r : ((Coord × Base → Binary) ⧸ T) →ₗ[Binary] ((Base → Binary) ⧸ B))
    (hq : ∀ t ∈ L, ∀ v, q (S.mkQ (labelTensor p t v)) = if t = s then A.mkQ v else 0)
    (hr : ∀ t ∈ L, ∀ v, r (T.mkQ (labelTensor p t v)) = if t = s then B.mkQ v else 0)
    (h : PureAnnihilates (∑ t ∈ L, block p t (Z t)) S T) :
    PureAnnihilates (Z s) A B

end Lax342547.TensorBlocks
end
