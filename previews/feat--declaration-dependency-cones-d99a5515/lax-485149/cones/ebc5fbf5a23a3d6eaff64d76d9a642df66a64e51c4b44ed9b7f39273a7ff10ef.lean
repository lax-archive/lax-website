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

-- Lax485149.Complement
section
namespace Lax485149
end Lax485149

namespace Lax485149.Complement
end Lax485149.Complement

namespace Lax485149.Complement.DecisionProblem
end Lax485149.Complement.DecisionProblem
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

-- Lax485149.TransitiveClosure
section
namespace Lax485149.TransitiveClosure

open Lax904597.Problems

open FirstOrder

open Language

/-- A single-`TC` definition: the transition formula of a graph on `k`-tuples,
together with formulas for the admissible start and end tuples. All three are
first-order over the ordered expansion of the vocabulary, so that they may
mention the linear order, as the ordered setting of the capture theorem
allows. -/
structure TCSpec (L : Language.{0, 0}) where
  /-- The *modes*: a finite amount of state the walk carries besides its tuple
  of elements. Tuples of elements cannot hold finite data of their own – a
  one-element universe has only one tuple – so, exactly as tags replace the
  order-encoded sorts of a textbook interpretation in `FOInterpretation`, a
  mode carries what the tuple cannot. -/
  Mode : Type
  /-- Modes are finite. -/
  [modeFinite : Finite Mode]
  /-- The arity: the walk runs on `k`-tuples of elements. -/
  k : ℕ
  /-- The transition formula, one per pair of modes, with two `k`-tuples of
  free variables: the current tuple on the left, the next one on the right. -/
  step : Mode → Mode → (L.sum Language.order).Formula (Fin k ⊕ Fin k)
  /-- The formula defining the admissible starting tuples, per mode. -/
  src : Mode → (L.sum Language.order).Formula (Fin k)
  /-- The formula defining the accepting tuples, per mode. -/
  tgt : Mode → (L.sum Language.order).Formula (Fin k)

attribute [instance] TCSpec.modeFinite

namespace TCSpec

section Semantics

variable {L : Language.{0, 0}} (spec : TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

end Semantics

end TCSpec

end Lax485149.TransitiveClosure
end

-- Lax485149.DeterministicTransitiveClosure
section
namespace Lax485149.DeterministicTransitiveClosure
end Lax485149.DeterministicTransitiveClosure

namespace Lax485149.DeterministicTransitiveClosure.TCSpec
end Lax485149.DeterministicTransitiveClosure.TCSpec
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

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax485149.ClassL
section
namespace Lax485149.ClassL
end Lax485149.ClassL
end

-- Lax485149.SecondOrderAtoms
section
namespace Lax485149
end Lax485149

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax485149.SecondOrderAtoms.SOAtom
end Lax485149.SecondOrderAtoms.SOAtom
end

-- Lax485149.KromFragment
section
namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax485149.KromFragment.KromClause
end Lax485149.KromFragment.KromClause

namespace Lax485149.KromFragment.KromLit
end Lax485149.KromFragment.KromLit

namespace Lax485149.KromFragment.KromProgram
end Lax485149.KromFragment.KromProgram
end

-- Lax485149.ClassNL
section
namespace Lax485149.ClassNL
end Lax485149.ClassNL
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

-- Lax485149.Reachability
section
namespace Lax485149.Reachability
end Lax485149.Reachability

namespace Lax485149.Reachability.stGraphRel
end Lax485149.Reachability.stGraphRel

namespace Lax485149.Reachability.stGraphRel.edge
end Lax485149.Reachability.stGraphRel.edge

namespace Lax485149.Reachability.stGraphRel.source
end Lax485149.Reachability.stGraphRel.source

namespace Lax485149.Reachability.stGraphRel.target
end Lax485149.Reachability.stGraphRel.target
end

-- Lax485149.DeterministicReachability
section
namespace Lax485149.DeterministicReachability
end Lax485149.DeterministicReachability
end

-- Lax485149.FirstOrderDefinability
section
namespace Lax485149
end Lax485149

namespace Lax485149.FirstOrderDefinability
end Lax485149.FirstOrderDefinability
end

-- Lax485149.HeadAutomata
section
namespace Lax485149.HeadAutomata.HeadMove.Holds
end Lax485149.HeadAutomata.HeadMove.Holds

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

end HeadAutomaton

end Lax485149.HeadAutomata
end

-- Lax904597.Sat
section
namespace Lax904597.Sat

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

/-- The relation symbols of CNF instances. -/
inductive satRel : ℕ → Type where
  /-- `isClause c`: the element `c` is a clause. -/
  | isClause : satRel 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : satRel 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : satRel 2
  deriving DecidableEq

/-- The relational language of CNF instances: a unary predicate singling out
clauses, and two binary predicates for positive and negative occurrences of a
variable in a clause. -/
def sat : Language :=
  ⟨fun _ => Empty, satRel⟩

/-- `isClause c`: the element `c` is a clause. -/
abbrev satIsClause : sat.Relations 1 := .isClause

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev satPosIn : sat.Relations 2 := .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev satNegIn : sat.Relations 2 := .negIn

/-- A CNF instance is satisfiable if some assignment of truth values to its
elements makes every clause contain a true literal. -/
def Satisfiable (A : Type) [sat.Structure A] : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)

end Lax904597.Sat
end

-- Lax485149.TwoSat
section
namespace Lax485149.TwoSat

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open Lax904597.Problems Lax904597.Sat Lax485149.Problems

namespace SatOcc

variable {A : Type} [sat.Structure A]

/-- `c` is a clause. -/
def IsCl (c : A) : Prop := RelMap satIsClause ![c]

/-- `x` occurs positively in `c`. -/
def PosIn (c x : A) : Prop := RelMap satPosIn ![c, x]

/-- `x` occurs negatively in `c`. -/
def NegIn (c x : A) : Prop := RelMap satNegIn ![c, x]

/-- The literal `(x, s)` occurs in the clause `c` (`s = true` for a positive
occurrence). Occurrences are restricted to actual clauses. -/
def OccIn (c x : A) (s : Bool) : Prop := IsCl c ∧ if s then PosIn c x else NegIn c x

end SatOcc

/-- Every clause has at most two literal occurrences: among any three
occurrences of a clause, two coincide (as signed occurrences). -/
def WidthAtMostTwo (A : Type) [sat.Structure A] : Prop :=
  ∀ (c : A) (x : Fin 3 → A) (s : Fin 3 → Bool),
    (∀ i, SatOcc.OccIn c (x i) (s i)) → ∃ i j, i ≠ j ∧ x i = x j ∧ s i = s j

/-- A CNF instance is a yes-instance of 2SAT if every clause has at most two
literal occurrences and the CNF is satisfiable. -/
def TwoSatisfiable (A : Type) [sat.Structure A] : Prop :=
  WidthAtMostTwo A ∧ Satisfiable A

end Lax485149.TwoSat
end

-- Lax485149.TwoSatInvariance
section
namespace Lax485149.TwoSatInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Sat

open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment

open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure

open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability

open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- Being satisfiable of width at most two is isomorphism-invariant. -/
axiom twoSatisfiable_iso : ∀ {A B : Type} [sat.Structure A] [sat.Structure B],
  (A ≃[sat] B) → (TwoSatisfiable A ↔ TwoSatisfiable B)

end Lax485149.TwoSatInvariance
end
