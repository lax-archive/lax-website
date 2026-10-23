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

namespace Lax434175.Precedence.Order.InClass
end Lax434175.Precedence.Order.InClass

namespace Lax434175.Precedence.Order.embed
end Lax434175.Precedence.Order.embed

namespace Lax434175.Precedence.Order.le
end Lax434175.Precedence.Order.le

namespace Lax434175.Precedence

open Lax434175.Kernels Lax434175.Modules

inductive Order
  | none
  | chains
  | intree
  | outtree
  | tree
  | opposingForest
  | seriesParallel
  | divideAndConquer
  | intervalOrder
  | quasiInterval
  | overInterval
  | aOrder
  | levelOrder
  | boundedHeight
  | dimensionTwo
  | boundedDimension
  | prec
  deriving DecidableEq

/-- No data without precedence constraints; a relation on the jobs with them. -/
def Order.Data (n : ℕ) : Order → Type
  | .none => Unit
  | _ => Fin n → Fin n → Prop

/-- The precedence relation; empty when the class is none. -/
def Order.view {n : ℕ} : (v : Order) → v.Data n → Fin n → Fin n → Prop
  | .none, _ => fun _ _ => False
  | .chains, r | .intree, r | .outtree, r | .tree, r | .opposingForest, r
  | .seriesParallel, r | .divideAndConquer, r | .intervalOrder, r | .levelOrder, r | .boundedHeight, r
  | .quasiInterval, r | .overInterval, r | .aOrder, r
  | .dimensionTwo, r
  | .boundedDimension, r | .prec, r => r

end Lax434175.Precedence
end

-- Lax434175.PrecedenceReversal
section
namespace Lax434175.PrecedenceReversal.lagsReverseData
end Lax434175.PrecedenceReversal.lagsReverseData

namespace Lax434175.PrecedenceReversal.reversible
end Lax434175.PrecedenceReversal.reversible

namespace Lax434175.PrecedenceReversal

open Lax434175.Precedence

/-- The class of the reverses of the relations of a class. -/
def reverse : Order → Order
  | .intree => .outtree
  | .outtree => .intree
  | o => o

/-- The reversed relation of a value. -/
def reverseData {n : ℕ} : (o : Order) → o.Data n → (reverse o).Data n
  | .none, _ => ()
  | .chains, r | .intree, r | .outtree, r | .tree, r | .opposingForest, r
  | .seriesParallel, r | .divideAndConquer, r | .intervalOrder, r | .quasiInterval, r
  | .overInterval, r | .aOrder, r | .levelOrder, r | .boundedHeight, r | .dimensionTwo, r
  | .boundedDimension, r | .prec, r => fun i j => r j i

axiom view_reverse {n : ℕ} (o : Order) (d : o.Data n) (i j : Fin n) :
    (reverse o).view (reverseData o d) i j ↔ o.view d j i

end Lax434175.PrecedenceReversal
end
