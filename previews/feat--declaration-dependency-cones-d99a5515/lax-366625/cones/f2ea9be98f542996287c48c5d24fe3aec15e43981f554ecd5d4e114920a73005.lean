-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

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

-- Lax904597.Relativized
section
namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.Relativized.RelFOInterpretation
end Lax904597.Relativized.RelFOInterpretation

namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction
end

-- Lax366625.CountingProblems
section
namespace Lax366625
end Lax366625

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.CountingProblems.CountingProblem
end Lax366625.CountingProblems.CountingProblem

namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction
end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems.CountingProblem.ofFun
end Lax366625.CountingProblems.CountingProblem.ofFun
end

-- Lax485149.Problems
section
namespace Lax485149
end Lax485149

namespace Lax485149.Problems
end Lax485149.Problems

namespace Lax485149.Problems.DecisionProblem
end Lax485149.Problems.DecisionProblem

namespace Lax485149.Problems.DecisionProblem.ofPred
end Lax485149.Problems.DecisionProblem.ofPred
end

-- Lax535992.CircuitValue
section
namespace Lax535992
end Lax535992

namespace Lax535992.CircuitValue
end Lax535992.CircuitValue

namespace Lax535992.CircuitValue.GateVal
end Lax535992.CircuitValue.GateVal

namespace Lax535992.CircuitValue.circuitRel
end Lax535992.CircuitValue.circuitRel

namespace Lax535992.CircuitValue.circuitRel.isAnd
end Lax535992.CircuitValue.circuitRel.isAnd

namespace Lax535992.CircuitValue.circuitRel.isFalse
end Lax535992.CircuitValue.circuitRel.isFalse

namespace Lax535992.CircuitValue.circuitRel.isNot
end Lax535992.CircuitValue.circuitRel.isNot

namespace Lax535992.CircuitValue.circuitRel.isOr
end Lax535992.CircuitValue.circuitRel.isOr

namespace Lax535992.CircuitValue.circuitRel.isTrue
end Lax535992.CircuitValue.circuitRel.isTrue

namespace Lax535992.CircuitValue.circuitRel.left
end Lax535992.CircuitValue.circuitRel.left

namespace Lax535992.CircuitValue.circuitRel.out
end Lax535992.CircuitValue.circuitRel.out

namespace Lax535992.CircuitValue.circuitRel.right
end Lax535992.CircuitValue.circuitRel.right
end

-- Lax366625.NumberedCircuits
section
namespace Lax366625.NumberedCircuits.circuitOfNum
end Lax366625.NumberedCircuits.circuitOfNum

namespace Lax366625.NumberedCircuits

open Lax535992.CircuitValue

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive numCircuitRel : ℕ → Type where
/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
  | isTrue : numCircuitRel 1
/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
  | isFalse : numCircuitRel 1
/-- `isAnd g`: the element `g` is a conjunction gate. -/
  | isAnd : numCircuitRel 1
/-- `isOr g`: the element `g` is a disjunction gate. -/
  | isOr : numCircuitRel 1
/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
  | isNot : numCircuitRel 1
/-- `out g`: the element `g` is an output gate, holding one digit. -/
  | out : numCircuitRel 1
/-- `left g x`: the gate `g` takes `x` as its first argument. -/
  | left : numCircuitRel 2
/-- `right g x`: the gate `g` takes `x` as its second argument. -/
  | right : numCircuitRel 2
/-- `below h g`: the digit held by `h` is at most as significant as the one
  held by `g`. -/
  | below : numCircuitRel 2
  deriving DecidableEq

/-- The relational language of Boolean circuits writing a number: the symbols
of circuits, and a comparison of the output gates. -/
def numCircuit : FirstOrder.Language :=
  ⟨fun _ => Empty, numCircuitRel⟩

open FirstOrder

open Language Structure

section Semantics

variable {A : Type} [numCircuit.Structure A]

end Semantics

open Lax366625.CountingProblems

end Lax366625.NumberedCircuits
end
