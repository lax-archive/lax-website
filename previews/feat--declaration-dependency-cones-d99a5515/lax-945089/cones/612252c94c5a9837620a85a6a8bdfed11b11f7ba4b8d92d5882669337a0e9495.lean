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
namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax535992.InflationaryFixedPoint

open Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A simultaneous first-order induction: a block of relation variables, one
first-order step formula per variable – over the base vocabulary expanded by
the block, its free variables the arguments of the variable – and an output
sentence over the same expanded vocabulary, read at the value of the
iteration. The step formulas are *unrestricted*. -/
structure StepDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the iteration. -/
  B : SOBlock
  /-- The step formula of each variable; its free variables are the arguments
  of the variable. -/
  step : ∀ i : B.ι, (L.sum B.lang).Formula (Fin (B.arity i))
  /-- The first-order output, over the expanded vocabulary – unrestricted, in
  particular free to negate fixed-point atoms. -/
  out : (L.sum B.lang).Sentence

namespace StepDef

variable {L : Language.{0, 0}} (d : StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

end Semantics

end StepDef

end Lax535992.InflationaryFixedPoint
end

-- Lax945089.EhrenfeuchtGames
section
namespace Lax945089.EhrenfeuchtGames.efStage
end Lax945089.EhrenfeuchtGames.efStage

namespace Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- The quantifier depth of a bounded formula: the number of pebbles the
invariance argument spends on it. -/
def qdepth {L : Language.{0, 0}} {α : Type*} : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp f₁ f₂ => max (qdepth f₁) (qdepth f₂)
  | _, .all f => qdepth f + 1

end Lax945089.EhrenfeuchtGames
end

-- Lax945089.PebbleGames
section
namespace Lax945089.PebbleGames.PebbleRel₂
end Lax945089.PebbleGames.PebbleRel₂

namespace Lax945089.PebbleGames.RelsIn
end Lax945089.PebbleGames.RelsIn

namespace Lax945089.PebbleGames.blockRelsExtend
end Lax945089.PebbleGames.blockRelsExtend

namespace Lax945089.PebbleGames.pebbleStage₂
end Lax945089.PebbleGames.pebbleStage₂

namespace Lax945089.PebbleGames

open Lax904597.SecondOrder Lax535992.InflationaryFixedPoint Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- The variable budget of a simultaneous induction: `k` covers each
variable's arity together with the quantifier depth of its step formula –
enough pebbles to hold the arguments and play out the quantifiers. -/
def StepDef.VarBound {L : Language.{0, 0}} (d : StepDef L) (k : ℕ) : Prop :=
  ∀ i, d.B.arity i + qdepth (d.step i) ≤ k

variable {M N : Type} {k : ℕ}

end Lax945089.PebbleGames
end
