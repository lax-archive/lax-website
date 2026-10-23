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

instance instIsRelationalCircuit : FirstOrder.Language.IsRelational circuit := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Semantics

variable {A : Type} [circuit.Structure A]

end Semantics

end Lax535992.CircuitValue
end

-- Lax366625.NumberedCircuits
section
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

/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
abbrev ncIsTrue : numCircuit.Relations 1 :=
  .isTrue

/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
abbrev ncIsFalse : numCircuit.Relations 1 :=
  .isFalse

/-- `isAnd g`: the element `g` is a conjunction gate. -/
abbrev ncIsAnd : numCircuit.Relations 1 :=
  .isAnd

/-- `isOr g`: the element `g` is a disjunction gate. -/
abbrev ncIsOr : numCircuit.Relations 1 :=
  .isOr

/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
abbrev ncIsNot : numCircuit.Relations 1 :=
  .isNot

/-- `out g`: the element `g` is an output gate, holding one digit. -/
abbrev ncOut : numCircuit.Relations 1 :=
  .out

/-- `left g x`: the gate `g` takes `x` as its first argument. -/
abbrev ncLeft : numCircuit.Relations 2 :=
  .left

/-- `right g x`: the gate `g` takes `x` as its second argument. -/
abbrev ncRight : numCircuit.Relations 2 :=
  .right

open FirstOrder

open Language Structure

/-- Forgetting the comparison of the outputs: the vocabulary of circuits, read
in the vocabulary of circuits writing a number. -/
def circuitOfNum : circuit →ᴸ numCircuit where
  onFunction := fun {_} f => isEmptyElim f
  onRelation := fun {n} R =>
    match n, R with
    | _, .isTrue => ncIsTrue
    | _, .isFalse => ncIsFalse
    | _, .isAnd => ncIsAnd
    | _, .isOr => ncIsOr
    | _, .isNot => ncIsNot
    | _, .out => ncOut
    | _, .left => ncLeft
    | _, .right => ncRight

/-- A circuit writing a number is a circuit. -/
instance numCircuitStructure (A : Type) [numCircuit.Structure A] :
    circuit.Structure A :=
  circuitOfNum.reduct A

section Semantics

variable {A : Type} [numCircuit.Structure A]

end Semantics

open Lax366625.CountingProblems

end Lax366625.NumberedCircuits
end
