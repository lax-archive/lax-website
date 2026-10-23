-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Complexity
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
namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction

namespace Lax904597.Interpretations

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A tagged `dim`-dimensional first-order interpretation of `L'` in `L`:
the defining `L`-formula of each relation symbol of `L'`, for each tuple of
tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
argument tuple. -/
structure FOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) where
  /-- The defining `L`-formula of each relation symbol of `L'`, for each tuple
  of tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
  argument tuple. -/
  relFormula : ∀ {n : ℕ}, L'.Relations n → (Fin n → Tag) → L.Formula (Fin n × Fin dim)

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

end FOInterpretation

section Ordered

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [LE A]

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

end Ordered

end Lax904597.Interpretations
end

-- Lax485149.HeadAutomata
section
namespace Lax485149.HeadAutomata

open FirstOrder

open Language Structure

/-- What a head may do in one step: stay where it is, jump to an end of the
order, copy another head, or step to the immediate successor or predecessor of
another head. All of it is definable from the order, which is what lets a
transition become a first-order formula. -/
inductive HeadMove (k : ℕ) where
  /-- Stay on the current element. -/
  | stay : HeadMove k
  /-- Jump to the least element. -/
  | toMin : HeadMove k
  /-- Jump to the greatest element. -/
  | toMax : HeadMove k
  /-- Copy the position of head `i`. -/
  | copy (i : Fin k) : HeadMove k
  /-- Move to the immediate successor of head `i` (disabled at the greatest
  element, which is how a head runs off the end). -/
  | succ (i : Fin k) : HeadMove k
  /-- Move to the immediate predecessor of head `i` (disabled at the least
  element). -/
  | pred (i : Fin k) : HeadMove k
  deriving DecidableEq

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

/-- The semantics of a move: where head `j` may be after it, the current heads
being `x`. -/
def Holds (mv : HeadMove k) (x : Fin k → A) (j : Fin k) (y : A) : Prop :=
  match mv with
  | .stay => y = x j
  | .toMin => ∀ b : A, y ≤ b
  | .toMax => ∀ b : A, b ≤ y
  | .copy i => y = x i
  | .succ i => x i < y ∧ ∀ a : A, ¬(x i < a ∧ a < y)
  | .pred i => y < x i ∧ ∀ a : A, ¬(y < a ∧ a < x i)

end HeadMove

/-- **A two-way `k`-head automaton over `L`-structures**: a finite control, a
finite list of quantifier-free tests of the head positions, and, per state and
per outcome of those tests, a list of possible transitions – a new state and one
move per head. No work tape: all the storage is in the `k` heads. -/
structure HeadAutomaton (L : Language.{0, 0}) (k : ℕ) where
  /-- The control states. -/
  State : Type
  /-- The control is finite: that is what makes this a machine. -/
  [stateFinite : Finite State]
  /-- The initial state. -/
  start : State
  /-- The accepting states. -/
  accept : State → Bool
  /-- What the control reads at each step, indexed by a finite type. -/
  TestIx : Type
  /-- Finitely many tests: a control that could read unboundedly many facts
  would not be a finite control. -/
  [testFinite : Finite TestIx]
  /-- The tests: what the control sees of the current head positions. -/
  test : TestIx → (L.sum Language.order).Formula (Fin k)
  /-- **The tests are quantifier-free.** The control may compare its heads and
  look at the relations holding between them, and nothing else; a quantified
  test would make the model first-order logic in disguise. -/
  test_qf : ∀ i, (test i).IsQF
  /-- The transitions available in a state, at a given outcome of the tests:
  a new state and a move for each head. Nondeterminism is the length of this
  list. -/
  trans : State → (TestIx → Bool) → List (State × (Fin k → HeadMove k))

attribute [instance] HeadAutomaton.stateFinite HeadAutomaton.testFinite

namespace HeadAutomaton

variable {L : Language.{0, 0}} {k : ℕ} (M : HeadAutomaton L k) {A : Type} [L.Structure A]
  [LinearOrder A]

/-- A configuration: a control state together with the positions of the heads. -/
abbrev Config (A : Type) : Type := M.State × (Fin k → A)

open Classical in
/-- What the control reads at a configuration: the truth values of its tests. -/
noncomputable def reading (x : Fin k → A) : M.TestIx → Bool :=
  fun i => decide ((M.test i).Realize x)

/-- One step of the automaton: some transition available at the current state
and reading leads to the new state, each head moving as it prescribes. -/
def Step (a b : M.Config A) : Prop :=
  ∃ p ∈ M.trans a.1 (M.reading a.2), p.1 = b.1 ∧ ∀ j, (p.2 j).Holds a.2 j (b.2 j)

/-- The automaton accepts the structure when an accepting state is reachable
from an initial configuration – the initial state with every head on the least
element. -/
def Accepts (A : Type) [L.Structure A] [LinearOrder A] : Prop :=
  ∃ c₀ c : M.Config A, (c₀.1 = M.start ∧ ∀ j, ∀ b : A, c₀.2 j ≤ b) ∧
    Relation.ReflTransGen M.Step c₀ c ∧ M.accept c.1 = true

end HeadAutomaton

end Lax485149.HeadAutomata
end
