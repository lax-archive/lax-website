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
end Lax342547.SparsePins
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
