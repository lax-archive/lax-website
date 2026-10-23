-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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
namespace Lax535992.CircuitValue.GateVal
end Lax535992.CircuitValue.GateVal

namespace Lax535992.CircuitValue

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive circuitRel : ℕ → Type where
/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
  | isTrue : circuitRel 1
/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
  | isFalse : circuitRel 1
/-- `isAnd g`: the element `g` is a conjunction gate. -/
  | isAnd : circuitRel 1
/-- `isOr g`: the element `g` is a disjunction gate. -/
  | isOr : circuitRel 1
/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
  | isNot : circuitRel 1
/-- `out g`: the element `g` is an output gate. -/
  | out : circuitRel 1
/-- `left g x`: the gate `g` takes `x` as its first argument. -/
  | left : circuitRel 2
/-- `right g x`: the gate `g` takes `x` as its second argument. -/
  | right : circuitRel 2
  deriving DecidableEq

/-- The relational language of Boolean circuits: one unary predicate per gate
kind, one marking the output, and two binary predicates wiring a gate to its
arguments. -/
def circuit : FirstOrder.Language :=
  ⟨fun _ => Empty, circuitRel⟩

/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
abbrev circIsTrue : circuit.Relations 1 :=
  .isTrue

open FirstOrder

open Language Structure

section Semantics

variable {A : Type} [circuit.Structure A]

end Semantics

end Lax535992.CircuitValue
end
