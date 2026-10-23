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

namespace Lax945089.PebbleGames.pebbleStage₂
end Lax945089.PebbleGames.pebbleStage₂

namespace Lax945089.PebbleGames

open Lax904597.SecondOrder Lax535992.InflationaryFixedPoint Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- A relation between `k`-tuples of two types: the positions of the
two-structure `k`-pebble game. -/
abbrev PebbleRel₂ (M N : Type) (k : ℕ) : Type :=
  (Fin k → M) → (Fin k → N) → Prop

variable {M N : Type} {k : ℕ}

/-- Agreement on the atomic type between tuples of two structures: the same
equalities between coordinates, and the same base relations of the family `S`
at every selection of coordinates. -/
def atomicAgreeOn₂ {L : Language.{0, 0}} (S : Set (Σ n, L.Relations n)) (M N : Type)
    [L.Structure M] [L.Structure N]
    (k : ℕ) : PebbleRel₂ M N k :=
  fun v w =>
    (∀ i j : Fin k, v i = v j ↔ w i = w j) ∧
    ∀ {l : ℕ} (R : L.Relations l), ⟨l, R⟩ ∈ S → ∀ g : Fin l → Fin k,
      ((RelMap R fun p => v (g p)) ↔ RelMap R fun p => w (g p))

end Lax945089.PebbleGames
end
