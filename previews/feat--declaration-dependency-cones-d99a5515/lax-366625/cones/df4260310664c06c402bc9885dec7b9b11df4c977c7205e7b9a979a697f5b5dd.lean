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
namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction
end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems

open Lax904597.Interpretations Lax904597.Problems Lax904597.Relativized

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-- A counting problem: an isomorphism-invariant natural number attached to
every `L`-structure. Only the values on finite structures are ever read. -/
structure CountingProblem [L.IsRelational] where
  /-- The count: `C A` (through the function coercion) is the number attached
  to the structure `A`. -/
  Count : ∀ (A : Type) [L.Structure A], ℕ
  /-- Counting problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → Count A = Count B

namespace CountingProblem

variable {L} [L.IsRelational]

/-- The counting problem given by a number attached to every structure: the
least value it takes on the structures isomorphic to a given one, which is
invariant by construction. When the number is itself invariant, this is the
number. -/
noncomputable def ofFun (f : ∀ (A : Type) [L.Structure A], ℕ) : CountingProblem L where
  Count := fun A _ =>
    sInf {n : ℕ | ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @f B i = n}
  iso_invariant := fun e =>
    congrArg sInf (Set.ext fun _ =>
      ⟨fun ⟨B, i, g, h⟩ => ⟨B, i, e.comp g, h⟩, fun ⟨B, i, g, h⟩ => ⟨B, i, e.symm.comp g, h⟩⟩)

end CountingProblem

variable {L} {L' : Language.{0, 0}}

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

end Lax366625.CountingProblems
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

/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
abbrev circIsTrue : circuit.Relations 1 :=
  .isTrue

/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
abbrev circIsFalse : circuit.Relations 1 :=
  .isFalse

/-- `isAnd g`: the element `g` is a conjunction gate. -/
abbrev circIsAnd : circuit.Relations 1 :=
  .isAnd

/-- `isOr g`: the element `g` is a disjunction gate. -/
abbrev circIsOr : circuit.Relations 1 :=
  .isOr

/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
abbrev circIsNot : circuit.Relations 1 :=
  .isNot

/-- `left g x`: the gate `g` takes `x` as its first argument. -/
abbrev circLeft : circuit.Relations 2 :=
  .left

/-- `right g x`: the gate `g` takes `x` as its second argument. -/
abbrev circRight : circuit.Relations 2 :=
  .right

open FirstOrder

open Language Structure

section Semantics

variable {A : Type} [circuit.Structure A]

/-- **The value derivable at a gate**, as one inductive family indexed by the
value being derived: `GateVal true g` says that `g` evaluates to `1`,
`GateVal false g` that it evaluates to `0`. Being an inductive predicate, it is
the *least* pair of rails closed under the gate rules, so a gate whose
arguments derive nothing – including one on a cycle – derives nothing.

The rules are the usual ones read in both polarities: a conjunction is true
when both arguments are, false as soon as one is; a disjunction dually; a
negation swaps the rails. -/
inductive GateVal : Bool → A → Prop
  /-- A constant `1` input derives `true`. -/
  | constTrue {g : A} (h : RelMap circIsTrue ![g]) : GateVal true g
  /-- A constant `0` input derives `false`. -/
  | constFalse {g : A} (h : RelMap circIsFalse ![g]) : GateVal false g
  /-- A conjunction with both arguments true derives `true`. -/
  | andTrue {g l r : A} (hg : RelMap circIsAnd ![g]) (hl : RelMap circLeft ![g, l])
      (hr : RelMap circRight ![g, r]) (vl : GateVal true l) (vr : GateVal true r) :
      GateVal true g
  /-- A conjunction with a false first argument derives `false`. -/
  | andFalseLeft {g l : A} (hg : RelMap circIsAnd ![g]) (hl : RelMap circLeft ![g, l])
      (vl : GateVal false l) : GateVal false g
  /-- A conjunction with a false second argument derives `false`. -/
  | andFalseRight {g r : A} (hg : RelMap circIsAnd ![g]) (hr : RelMap circRight ![g, r])
      (vr : GateVal false r) : GateVal false g
  /-- A disjunction with a true first argument derives `true`. -/
  | orTrueLeft {g l : A} (hg : RelMap circIsOr ![g]) (hl : RelMap circLeft ![g, l])
      (vl : GateVal true l) : GateVal true g
  /-- A disjunction with a true second argument derives `true`. -/
  | orTrueRight {g r : A} (hg : RelMap circIsOr ![g]) (hr : RelMap circRight ![g, r])
      (vr : GateVal true r) : GateVal true g
  /-- A disjunction with both arguments false derives `false`. -/
  | orFalse {g l r : A} (hg : RelMap circIsOr ![g]) (hl : RelMap circLeft ![g, l])
      (hr : RelMap circRight ![g, r]) (vl : GateVal false l) (vr : GateVal false r) :
      GateVal false g
  /-- A negation with a false argument derives `true`. -/
  | notTrue {g i : A} (hg : RelMap circIsNot ![g]) (hi : RelMap circLeft ![g, i])
      (vi : GateVal false i) : GateVal true g
  /-- A negation with a true argument derives `false`. -/
  | notFalse {g i : A} (hg : RelMap circIsNot ![g]) (hi : RelMap circLeft ![g, i])
      (vi : GateVal true i) : GateVal false g

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

instance instIsRelationalNumCircuit : FirstOrder.Language.IsRelational numCircuit := fun _ =>
  (inferInstance : IsEmpty Empty)

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

/-- `below h g`: the digit held by `h` is at most as significant as the one
  held by `g`. -/
abbrev ncBelow : numCircuit.Relations 2 :=
  .below

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

/-- The output gate `g` holds the digit `1`. -/
def OutBit (g : A) : Prop :=
  RelMap ncOut ![g] ∧ GateVal true g

/-- `h` is an output gate strictly below `g`. -/
def LowerOut (g h : A) : Prop :=
  RelMap ncOut ![h] ∧ h ≠ g ∧ RelMap ncBelow ![h, g]

/-- The rank of a gate among the outputs: the number of output gates strictly
below it. -/
noncomputable def outRank (g : A) : ℕ :=
  Nat.card {h : A // LowerOut g h}

variable (A) in
/-- **The comparison of the outputs is a linear order on them**: reflexive,
transitive, antisymmetric and total among the output gates. -/
def OutOrder : Prop :=
  (∀ p : A, RelMap ncOut ![p] → RelMap ncBelow ![p, p]) ∧
    (∀ p q r : A, RelMap ncOut ![p] → RelMap ncOut ![q] → RelMap ncOut ![r] →
      RelMap ncBelow ![p, q] → RelMap ncBelow ![q, r] → RelMap ncBelow ![p, r]) ∧
    (∀ p q : A, RelMap ncOut ![p] → RelMap ncOut ![q] →
      RelMap ncBelow ![p, q] → RelMap ncBelow ![q, p] → p = q) ∧
    ∀ p q : A, RelMap ncOut ![p] → RelMap ncOut ![q] →
      RelMap ncBelow ![p, q] ∨ RelMap ncBelow ![q, p]

variable (A) in
open Classical in
/-- **The number written by a circuit**: each output gate deriving the value
`1` contributes two to the power of its rank among the outputs; `0` unless the
outputs are linearly ordered. -/
noncomputable def circuitNumber : ℕ :=
  if OutOrder A then ∑ᶠ g : A, if OutBit g then 2 ^ outRank g else 0 else 0

end Semantics

open Lax366625.CountingProblems

/-- **The number written by a circuit**, as a counting problem. -/
noncomputable def CircuitNumber : CountingProblem numCircuit :=
  CountingProblem.ofFun fun A _ => circuitNumber A

end Lax366625.NumberedCircuits
end
