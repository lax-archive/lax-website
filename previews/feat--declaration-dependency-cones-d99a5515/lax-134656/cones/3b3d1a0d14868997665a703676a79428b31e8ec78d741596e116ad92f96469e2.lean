-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
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

-- Lax134656.SecondOrderTransitiveClosure
section
namespace Lax134656
end Lax134656

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec
end Lax134656.SecondOrderTransitiveClosure.SOTCSpec
end

-- Lax134656.OrderFreeTransitiveClosure
section
namespace Lax134656.OrderFreeTransitiveClosure

open Lax904597.Problems Lax904597.SecondOrder Lax535992.InflationaryFixedPoint

open Lax134656.SecondOrderTransitiveClosure

open FirstOrder

open Language Structure

/-- An SO(TC) specification that does **not** see a linear order: as in
`SOTCSpec`, the states of the walk are the assignments of
a block, but the three sentences live over the bare vocabulary expanded by
copies of the block, with no order symbol available. -/
structure SOTCSpecFree (L : Language.{0, 0}) : Type 1 where
  /-- The block whose assignments are the states of the walk. -/
  B : SOBlock
  /-- The transition sentence, over two copies of the block: the current state
  reads the first copy, the next state the second. -/
  step : ((L.sum B.lang).sum B.lang).Sentence
  /-- The sentence defining the admissible starting states. -/
  src : (L.sum B.lang).Sentence
  /-- The sentence defining the accepting states. -/
  tgt : (L.sum B.lang).Sentence

namespace SOTCSpecFree

section Semantics

variable {L : Language.{0, 0}} (spec : SOTCSpecFree L) {A : Type} [L.Structure A]

end Semantics

end SOTCSpecFree

end Lax134656.OrderFreeTransitiveClosure
end
