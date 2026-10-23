-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Projection

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

def tableSpace {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary) where
  carrier := {v | ∀ i, primalProjection i v ∈ projected P i a}
  zero_mem' := fun i => (projected P i a).zero_mem
  add_mem' := fun hv hw i => (projected P i a).add_mem (hv i) (hw i)
  smul_mem' := fun c _ hv i => (projected P i a).smul_mem c (hv i)

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

def Excludes
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) : Prop :=
  ∀ (a : Comp × Bool) (L : Fin 2 → Finset (Fin b → Binary))
    (c : Fin 2 → (Fin b → Binary) → Binary)
    (z : Fin 2 → (Fin b → Binary) → Base → Binary),
    (∀ i, (L i).card ≤ 14) → (∀ i, Disjoint (L i) (A i)) →
    (∑ i : Fin 2, ∑ s ∈ L i, c i s •
      primalEmbedding i (point (selectorEval (degree := degree)) s (z i s))) ∈ tableSpace P a →
    ∀ i s, s ∈ L i → c i s = 0

end Lax342547.KeySpans
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

axiom keys_exclusion {R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R) : Excludes P A

end Lax342547.PinLabelExclusions
end
