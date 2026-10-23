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

/-- The relational vocabulary of a block: one relation symbol per relation
variable. -/
def SOBlock.lang (B : SOBlock) : Language :=
  ⟨fun _ => Empty, fun n => {i : B.ι // B.arity i = n}⟩

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
namespace Lax945089.PebbleGames.PebbleRel₂
end Lax945089.PebbleGames.PebbleRel₂

namespace Lax945089.PebbleGames.RelsIn
end Lax945089.PebbleGames.RelsIn

namespace Lax945089.PebbleGames.StepDef
end Lax945089.PebbleGames.StepDef

namespace Lax945089.PebbleGames.pebbleStage₂
end Lax945089.PebbleGames.pebbleStage₂

namespace Lax945089.PebbleGames

open Lax904597.SecondOrder Lax535992.InflationaryFixedPoint Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- The agreement family of the block expansion of a structure: the given
family on the base symbols, everything on the block symbols. -/
def blockRelsExtend {L : Language.{0, 0}} (S : Set (Σ n, L.Relations n)) (B : SOBlock) :
    Set (Σ n, (L.sum B.lang).Relations n) :=
  fun x =>
    match x with
    | ⟨n, Sum.inl r⟩ => ⟨n, r⟩ ∈ S
    | ⟨_, Sum.inr _⟩ => True

variable {M N : Type} {k : ℕ}

end Lax945089.PebbleGames
end
