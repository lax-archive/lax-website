-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Logic.Relation

-- Lax434175.Kernels
section
namespace Lax434175
end Lax434175

namespace Lax434175.Kernels
end Lax434175.Kernels

namespace Lax434175.Kernels.Kernel
end Lax434175.Kernels.Kernel
end

-- Lax434175.Modules
section
namespace Lax434175.Modules
end Lax434175.Modules

namespace Lax434175.Modules.Module
end Lax434175.Modules.Module

namespace Lax434175.Modules.Objective
end Lax434175.Modules.Objective

namespace Lax434175.Modules.Module.Sound
end Lax434175.Modules.Module.Sound

namespace Lax434175.Modules.Objective.Sound
end Lax434175.Modules.Objective.Sound
end

-- Lax434175.Precedence
section
namespace Lax434175.Precedence.DivideAndConquer
end Lax434175.Precedence.DivideAndConquer

namespace Lax434175.Precedence.HasPath
end Lax434175.Precedence.HasPath

namespace Lax434175.Precedence.Lags
end Lax434175.Precedence.Lags

namespace Lax434175.Precedence.Order
end Lax434175.Precedence.Order

namespace Lax434175.Precedence.Value
end Lax434175.Precedence.Value

namespace Lax434175.Precedence.Lags.Admits
end Lax434175.Precedence.Lags.Admits

namespace Lax434175.Precedence.Lags.Data
end Lax434175.Precedence.Lags.Data

namespace Lax434175.Precedence.Lags.arbitrary
end Lax434175.Precedence.Lags.arbitrary

namespace Lax434175.Precedence.Lags.arbitraryNonpositive
end Lax434175.Precedence.Lags.arbitraryNonpositive

namespace Lax434175.Precedence.Lags.arbitraryPositive
end Lax434175.Precedence.Lags.arbitraryPositive

namespace Lax434175.Precedence.Lags.constant
end Lax434175.Precedence.Lags.constant

namespace Lax434175.Precedence.Lags.constantNonpositive
end Lax434175.Precedence.Lags.constantNonpositive

namespace Lax434175.Precedence.Lags.constantPositive
end Lax434175.Precedence.Lags.constantPositive

namespace Lax434175.Precedence.Lags.embed
end Lax434175.Precedence.Lags.embed

namespace Lax434175.Precedence.Lags.le
end Lax434175.Precedence.Lags.le

namespace Lax434175.Precedence.Lags.unit
end Lax434175.Precedence.Lags.unit

namespace Lax434175.Precedence.Lags.view
end Lax434175.Precedence.Lags.view

namespace Lax434175.Precedence.Lags.zero
end Lax434175.Precedence.Lags.zero

namespace Lax434175.Precedence.Order.Data
end Lax434175.Precedence.Order.Data

namespace Lax434175.Precedence.Order.InClass
end Lax434175.Precedence.Order.InClass

namespace Lax434175.Precedence.Order.aOrder
end Lax434175.Precedence.Order.aOrder

namespace Lax434175.Precedence.Order.boundedDimension
end Lax434175.Precedence.Order.boundedDimension

namespace Lax434175.Precedence.Order.boundedHeight
end Lax434175.Precedence.Order.boundedHeight

namespace Lax434175.Precedence.Order.chains
end Lax434175.Precedence.Order.chains

namespace Lax434175.Precedence.Order.dimensionTwo
end Lax434175.Precedence.Order.dimensionTwo

namespace Lax434175.Precedence.Order.divideAndConquer
end Lax434175.Precedence.Order.divideAndConquer

namespace Lax434175.Precedence.Order.embed
end Lax434175.Precedence.Order.embed

namespace Lax434175.Precedence.Order.intervalOrder
end Lax434175.Precedence.Order.intervalOrder

namespace Lax434175.Precedence.Order.intree
end Lax434175.Precedence.Order.intree

namespace Lax434175.Precedence.Order.le
end Lax434175.Precedence.Order.le

namespace Lax434175.Precedence.Order.levelOrder
end Lax434175.Precedence.Order.levelOrder

namespace Lax434175.Precedence.Order.none
end Lax434175.Precedence.Order.none

namespace Lax434175.Precedence.Order.opposingForest
end Lax434175.Precedence.Order.opposingForest

namespace Lax434175.Precedence.Order.outtree
end Lax434175.Precedence.Order.outtree

namespace Lax434175.Precedence.Order.overInterval
end Lax434175.Precedence.Order.overInterval

namespace Lax434175.Precedence.Order.prec
end Lax434175.Precedence.Order.prec

namespace Lax434175.Precedence.Order.quasiInterval
end Lax434175.Precedence.Order.quasiInterval

namespace Lax434175.Precedence.Order.seriesParallel
end Lax434175.Precedence.Order.seriesParallel

namespace Lax434175.Precedence.Order.tree
end Lax434175.Precedence.Order.tree

namespace Lax434175.Precedence.Order.view
end Lax434175.Precedence.Order.view

namespace Lax434175.Precedence

open Lax434175.Kernels Lax434175.Modules

/-- Five different jobs are related exactly by the pairs of a pattern. -/
def Contains {n : ℕ} (r : Fin n → Fin n → Prop) (pattern : List (Fin 5 × Fin 5)) : Prop :=
  ∃ f : Fin 5 → Fin n, Function.Injective f ∧
    ∀ a b, Relation.TransGen r (f a) (f b) ↔ (a, b) ∈ pattern

/-- Two unrelated pairs, the first job of one having a further successor. -/
def patternOut : List (Fin 5 × Fin 5) := [(0, 1), (2, 3), (2, 4)]

/-- The reverse of `patternOut`. -/
def patternIn : List (Fin 5 × Fin 5) := [(1, 0), (3, 2), (4, 2)]

/-- The third pattern forbidden in a quasi-interval order. -/
def patternThird : List (Fin 5 × Fin 5) := [(0, 1), (0, 3), (2, 3), (2, 4), (4, 3)]

/-- Neither `patternOut` nor its reverse occurs. -/
def OverInterval {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ¬ Contains r patternOut ∧ ¬ Contains r patternIn

/-- An over-interval order in which `patternThird` does not occur. -/
def QuasiInterval {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  OverInterval r ∧ ¬ Contains r patternThird

end Lax434175.Precedence
end
