-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.NNRat.Defs

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

-- Lax434175.Shops
section
namespace Lax434175.Shops.Machines
end Lax434175.Shops.Machines

namespace Lax434175.Shops.NoWait
end Lax434175.Shops.NoWait

namespace Lax434175.Shops.ProcessingTimes
end Lax434175.Shops.ProcessingTimes

namespace Lax434175.Shops.Sched
end Lax434175.Shops.Sched

namespace Lax434175.Shops.ShopType
end Lax434175.Shops.ShopType

namespace Lax434175.Shops.Machines.Data
end Lax434175.Shops.Machines.Data

namespace Lax434175.Shops.Machines.admits
end Lax434175.Shops.Machines.admits

namespace Lax434175.Shops.Machines.byPosition
end Lax434175.Shops.Machines.byPosition

namespace Lax434175.Shops.Machines.dedicated
end Lax434175.Shops.Machines.dedicated

namespace Lax434175.Shops.Machines.embed
end Lax434175.Shops.Machines.embed

namespace Lax434175.Shops.Machines.fix
end Lax434175.Shops.Machines.fix

namespace Lax434175.Shops.Machines.general
end Lax434175.Shops.Machines.general

namespace Lax434175.Shops.Machines.le
end Lax434175.Shops.Machines.le

namespace Lax434175.Shops.Machines.recirculation
end Lax434175.Shops.Machines.recirculation

namespace Lax434175.Shops.Machines.sets
end Lax434175.Shops.Machines.sets

namespace Lax434175.Shops.Machines.stages
end Lax434175.Shops.Machines.stages

namespace Lax434175.Shops.Machines.view
end Lax434175.Shops.Machines.view

namespace Lax434175.Shops.NoWait.constraint
end Lax434175.Shops.NoWait.constraint

namespace Lax434175.Shops.NoWait.noWait
end Lax434175.Shops.NoWait.noWait

namespace Lax434175.Shops.NoWait.none
end Lax434175.Shops.NoWait.none

namespace Lax434175.Shops.ProcessingTimes.arbitrary
end Lax434175.Shops.ProcessingTimes.arbitrary

namespace Lax434175.Shops.ProcessingTimes.equal
end Lax434175.Shops.ProcessingTimes.equal

namespace Lax434175.Shops.ProcessingTimes.holds
end Lax434175.Shops.ProcessingTimes.holds

namespace Lax434175.Shops.ProcessingTimes.rank
end Lax434175.Shops.ProcessingTimes.rank

namespace Lax434175.Shops.ProcessingTimes.unit
end Lax434175.Shops.ProcessingTimes.unit

namespace Lax434175.Shops.ShopType.flexibleFlow
end Lax434175.Shops.ShopType.flexibleFlow

namespace Lax434175.Shops.ShopType.flow
end Lax434175.Shops.ShopType.flow

namespace Lax434175.Shops.ShopType.holds
end Lax434175.Shops.ShopType.holds

namespace Lax434175.Shops.ShopType.job
end Lax434175.Shops.ShopType.job

namespace Lax434175.Shops.ShopType.le
end Lax434175.Shops.ShopType.le

namespace Lax434175.Shops.ShopType.open
end Lax434175.Shops.ShopType.open

namespace Lax434175.Shops.ShopType.ordered
end Lax434175.Shops.ShopType.ordered

namespace Lax434175.Shops

open Lax434175.Kernels Lax434175.Modules

structure Inst where
  jobs : ℕ
  machines : ℕ
  /-- The number of operations of a job. -/
  ops : Fin jobs → ℕ
  /-- The processing time of an operation. -/
  p : (j : Fin jobs) → Fin (ops j) → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ

end Lax434175.Shops
end

-- Lax434175.Transportation
section
namespace Lax434175.Transportation.Shape.le
end Lax434175.Transportation.Shape.le

namespace Lax434175.Transportation

open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

/-- The delays of an instance. -/
abbrev Delays (x : Inst) := (j : Fin x.jobs) → Fin (x.ops j) → Fin (x.ops j) → ℕ

inductive Shape
  | none
  | uniform
  | twoValues
  | job
  | source
  | jobSource
  | pairSymmetric
  | pair
  | jobPairSymmetric
  | jobPair
  deriving DecidableEq

/-- The delays of a shape. -/
def Shape.holds {x : Inst} : Shape → Delays x → Prop
  | .none, t => ∀ j k l, t j k l = 0
  | .uniform, t => ∃ T, ∀ j k l, t j k l = T
  | .twoValues, t => ∃ T₁ T₂, ∀ j, (∀ k l, t j k l = T₁) ∨ (∀ k l, t j k l = T₂)
  | .job, t => ∀ j k l k' l', t j k l = t j k' l'
  | .source, t => ∃ g : ℕ → ℕ, ∀ j k l, t j k l = g k.val
  | .jobSource, t => ∀ j k l l', t j k l = t j k l'
  | .pairSymmetric, t => ∃ g : ℕ → ℕ → ℕ, (∀ a b, g a b = g b a) ∧ ∀ j k l, t j k l = g k.val l.val
  | .pair, t => ∃ g : ℕ → ℕ → ℕ, ∀ j k l, t j k l = g k.val l.val
  | .jobPairSymmetric, t => ∀ j k l, t j k l = t j l k
  | .jobPair, _ => True

/-- The empty moving times of the robot, from a machine to a machine. -/
abbrev EmptyMoves (x : Inst) := Fin x.machines → Fin x.machines → ℕ

/-- A value of the field: a shape of delays, whether a robot carries the
jobs, and whether the robot needs time to travel empty. -/
structure Value where
  shape : Shape
  robot : Bool := false
  emptyMoves : Bool := false

/-- The data of the field: the delays and the empty moving times. -/
abbrev Data (x : Inst) := Delays x × EmptyMoves x

/-- The delays have the shape, and unless the value has a robot with empty
moves, the empty moving times are `0`. -/
def Value.admits {x : Inst} (v : Value) (d : Data x) : Prop :=
  v.shape.holds d.1 ∧ ((v.robot && v.emptyMoves) = false → ∀ i i', d.2 i i' = 0)

end Lax434175.Transportation
end
