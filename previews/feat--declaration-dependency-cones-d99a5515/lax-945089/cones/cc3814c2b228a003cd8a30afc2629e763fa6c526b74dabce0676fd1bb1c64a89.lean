-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax904597.Interpretations
section
namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Interpretations.FOInterpretation
end Lax904597.Interpretations.FOInterpretation

namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction
end

-- Lax904597.SecondOrder
section
namespace Lax904597.SecondOrder.SORealize
end Lax904597.SecondOrder.SORealize

namespace Lax904597.SecondOrder.soLang
end Lax904597.SecondOrder.soLang

namespace Lax904597.SecondOrder

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A second-order quantifier block: finitely many relation variables, with
given arities. The index type is arbitrary rather than an initial segment of
`ℕ`, so that constructions on blocks can build their natural index types. -/
structure SOBlock : Type 1 where
  /-- The index type of the relation variables of the block. -/
  ι : Type
  /-- A block has finitely many relation variables. -/
  [ιFinite : Finite ι]
  /-- The arity of each relation variable. -/
  arity : ι → ℕ

attribute [instance] SOBlock.ιFinite

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax535992.InflationaryFixedPoint
section
namespace Lax535992
end Lax535992

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax535992.InflationaryFixedPoint.StepDef
end Lax535992.InflationaryFixedPoint.StepDef
end

-- Lax945089.EhrenfeuchtGames
section
namespace Lax945089
end Lax945089

namespace Lax945089.EhrenfeuchtGames
end Lax945089.EhrenfeuchtGames

namespace Lax945089.EhrenfeuchtGames.efStage
end Lax945089.EhrenfeuchtGames.efStage

namespace Lax945089.EhrenfeuchtGames.qdepth
end Lax945089.EhrenfeuchtGames.qdepth
end

-- Lax945089.PebbleGames
section
namespace Lax945089.PebbleGames.RelsIn
end Lax945089.PebbleGames.RelsIn

namespace Lax945089.PebbleGames.StepDef
end Lax945089.PebbleGames.StepDef

namespace Lax945089.PebbleGames.blockRelsExtend
end Lax945089.PebbleGames.blockRelsExtend

namespace Lax945089.PebbleGames

open Lax904597.SecondOrder Lax535992.InflationaryFixedPoint Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- A relation between `k`-tuples of two types: the positions of the
two-structure `k`-pebble game. -/
abbrev PebbleRel₂ (M N : Type) (k : ℕ) : Type :=
  (Fin k → M) → (Fin k → N) → Prop

variable {M N : Type} {k : ℕ}

/-- The back-and-forth condition of the two-structure `k`-pebble game: the
pebble the spoiler moves, on either structure, can be answered on the other. -/
def PebbleBackForth₂ (E : PebbleRel₂ M N k) : PebbleRel₂ M N k :=
  fun a b => ∀ i : Fin k,
    (∀ c : M, ∃ d : N, E (Function.update a i c) (Function.update b i d)) ∧
    (∀ d : N, ∃ c : M, E (Function.update a i c) (Function.update b i d))

/-- One round of refinement. -/
def pebbleRefine₂ (E₀ E : PebbleRel₂ M N k) : PebbleRel₂ M N k :=
  fun a b => E₀ a b ∧ PebbleBackForth₂ E a b

/-- The descending refinement chain. -/
def pebbleStage₂ (E₀ : PebbleRel₂ M N k) : ℕ → PebbleRel₂ M N k
  | 0 => fun _ _ => True
  | n + 1 => pebbleRefine₂ E₀ (pebbleStage₂ E₀ n)

end Lax945089.PebbleGames
end
