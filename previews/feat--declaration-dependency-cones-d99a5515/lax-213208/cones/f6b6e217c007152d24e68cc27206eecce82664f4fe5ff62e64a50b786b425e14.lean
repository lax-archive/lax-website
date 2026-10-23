-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.DeriveFintype

-- Lax560851.StructuralPresentation
section
namespace Lax560851.StructuralPresentation.Raw.nodes
end Lax560851.StructuralPresentation.Raw.nodes

namespace Lax560851.StructuralPresentation

universe u

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

namespace Presentation

/-- Distinct values have distinct structural representations. -/
def Faithful {α : Type u} (P : Presentation α) : Prop :=
  Function.Injective P.toRaw

end Presentation

end Lax560851.StructuralPresentation
end

-- Lax560851.WordArena
section
namespace Lax560851.WordArena
end Lax560851.WordArena

namespace Lax560851.WordArena.WordImage
end Lax560851.WordArena.WordImage

namespace Lax560851.WordArena.encodeInto
end Lax560851.WordArena.encodeInto

namespace Lax560851.WordArena.WordImage.ChildAddress
end Lax560851.WordArena.WordImage.ChildAddress

namespace Lax560851.WordArena.WordImage.ReachableFrom
end Lax560851.WordArena.WordImage.ReachableFrom

namespace Lax560851.WordArena.WordImage.Represents
end Lax560851.WordArena.WordImage.Represents
end

-- Lax759944.BinaryWordEncoding
section
namespace Lax759944
end Lax759944

namespace Lax759944.BinaryWordEncoding
end Lax759944.BinaryWordEncoding

namespace Lax759944.BinaryWordEncoding.Symbol
end Lax759944.BinaryWordEncoding.Symbol

namespace Lax759944.BinaryWordEncoding.Symbol.one
end Lax759944.BinaryWordEncoding.Symbol.one

namespace Lax759944.BinaryWordEncoding.Symbol.separator
end Lax759944.BinaryWordEncoding.Symbol.separator

namespace Lax759944.BinaryWordEncoding.Symbol.zero
end Lax759944.BinaryWordEncoding.Symbol.zero
end

-- Lax213208.OptimizationProblem
section
namespace Lax213208.OptimizationProblem

open scoped NNReal

open Lax560851.StructuralPresentation Lax560851.WordArena

open Lax759944.BinaryWordEncoding

inductive Direction
  | minimize
  | maximize

structure Problem (Instance Solution : Type*) where
  direction : Direction
  feasible : Instance → Solution → Prop
  value : Instance → Solution → ℝ≥0
  input : Presentation Instance
  output : Solution → List ℕ
  input_faithful : input.Faithful
  output_injective : Function.Injective output

variable {Instance Solution : Type*}

end Lax213208.OptimizationProblem
end

-- Lax213208.Approximation
section
namespace Lax213208.Approximation

open OptimizationProblem

variable {Instance Solution : Type*}

def IsApproximation (problem : Problem Instance Solution)
    (r : ℝ) (x : Instance) (y : Solution) : Prop :=
  1 ≤ r ∧ problem.feasible x y ∧ ∀ z, problem.feasible x z →
    match problem.direction with
    | .minimize => (problem.value x y : ℝ) ≤ r * problem.value x z
    | .maximize => (problem.value x z : ℝ) ≤ r * problem.value x y

def IsOptimalValue (problem : Problem Instance Solution)
    (x : Instance) (value : ℝ) : Prop :=
  ∃ y, IsApproximation problem 1 x y ∧ (problem.value x y : ℝ) = value

end Lax213208.Approximation
end
