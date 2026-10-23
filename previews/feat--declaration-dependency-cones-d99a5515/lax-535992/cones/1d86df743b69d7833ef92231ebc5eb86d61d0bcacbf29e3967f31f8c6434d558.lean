-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.SetTheory.Cardinal.Finite

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

-- Lax535992.HornFragment
section
namespace Lax535992
end Lax535992

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.HornFragment.HornClause
end Lax535992.HornFragment.HornClause

namespace Lax535992.HornFragment.HornProgram
end Lax535992.HornFragment.HornProgram
end

-- Lax535992.ClassPTIME
section
namespace Lax535992.ClassPTIME
end Lax535992.ClassPTIME
end

-- Lax904597.Machines
section
namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Machines.Config
end Lax904597.Machines.Config

namespace Lax904597.Machines.TMData
end Lax904597.Machines.TMData

namespace Lax904597.Machines.turingRel
end Lax904597.Machines.turingRel

namespace Lax904597.Machines.Config.ext
end Lax904597.Machines.Config.ext

namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines.turingRel.acc
end Lax904597.Machines.turingRel.acc

namespace Lax904597.Machines.turingRel.blank
end Lax904597.Machines.turingRel.blank

namespace Lax904597.Machines.turingRel.inp
end Lax904597.Machines.turingRel.inp

namespace Lax904597.Machines.turingRel.le
end Lax904597.Machines.turingRel.le

namespace Lax904597.Machines.turingRel.posn
end Lax904597.Machines.turingRel.posn

namespace Lax904597.Machines.turingRel.right
end Lax904597.Machines.turingRel.right

namespace Lax904597.Machines.turingRel.start
end Lax904597.Machines.turingRel.start

namespace Lax904597.Machines.turingRel.tdst
end Lax904597.Machines.turingRel.tdst

namespace Lax904597.Machines.turingRel.tr
end Lax904597.Machines.turingRel.tr

namespace Lax904597.Machines.turingRel.tread
end Lax904597.Machines.turingRel.tread

namespace Lax904597.Machines.turingRel.tsrc
end Lax904597.Machines.turingRel.tsrc

namespace Lax904597.Machines.turingRel.twrite
end Lax904597.Machines.turingRel.twrite
end

-- Lax535992.DeterministicMachines
section
namespace Lax535992
end Lax535992

namespace Lax535992.DeterministicMachines
end Lax535992.DeterministicMachines

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData
end

-- Lax535992.Game
section
namespace Lax535992.Game

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive andOrGraphRel : ℕ → Type where
/-- `move a b`: the player to move at `a` may move to `b`. -/
  | move : andOrGraphRel 2
/-- `univ a`: the node `a` belongs to the universal player. -/
  | univ : andOrGraphRel 1
/-- `start a`: the node `a` is a marked starting position. -/
  | start : andOrGraphRel 1
/-- `won a`: the node `a` wins outright. -/
  | won : andOrGraphRel 1
  deriving DecidableEq

/-- The relational vocabulary of AND/OR graphs: a move relation, a mark for the
nodes of the universal player, a mark for the starting positions and a mark for
the positions that win outright. -/
def andOrGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, andOrGraphRel⟩

/-- `move a b`: the player to move at `a` may move to `b`. -/
abbrev agMove : andOrGraph.Relations 2 :=
  .move

/-- `univ a`: the node `a` belongs to the universal player. -/
abbrev agUniv : andOrGraph.Relations 1 :=
  .univ

/-- `start a`: the node `a` is a marked starting position. -/
abbrev agStart : andOrGraph.Relations 1 :=
  .start

/-- `won a`: the node `a` wins outright. -/
abbrev agWon : andOrGraph.Relations 1 :=
  .won

open FirstOrder

open Language Structure

section Defs

variable {A : Type} [andOrGraph.Structure A]

/-- `move a b`: the player to move at `a` may move to `b`.  -/
def AGMove {A : Type} [andOrGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agMove ![a0, a1]

/-- `univ a`: the node `a` belongs to the universal player.  -/
def AGUniv {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agUniv ![a0]

/-- `start a`: the node `a` is a marked starting position.  -/
def AGStart {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agStart ![a0]

/-- `won a`: the node `a` wins outright.  -/
def AGWon {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agWon ![a0]

variable (A) in
/-- **The winning positions of an AND/OR graph**, as a least fixed point: a
position that wins outright, an existential position with a winning successor,
or a universal position that has a successor and all of whose successors
win. -/
inductive WinsOn : A → Prop
  /-- A position that wins outright. -/
  | won {a : A} : AGWon a → WinsOn a
  /-- An existential position with a winning successor. -/
  | ex {a b : A} : ¬AGUniv a → AGMove a b → WinsOn b → WinsOn a
  /-- A universal position with a successor, all of whose successors win. -/
  | all {a : A} : AGUniv a → (∃ b, AGMove a b) → (∀ b, AGMove a b → WinsOn b) → WinsOn a

variable (A) in
/-- Some marked starting position is winning. -/
def GameWon : Prop := ∃ s : A, AGStart s ∧ WinsOn A s

end Defs

end Lax535992.Game
end

-- Lax904597.Sat
section
namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.Sat.satRel
end Lax904597.Sat.satRel

namespace Lax904597.Sat.satRel.isClause
end Lax904597.Sat.satRel.isClause

namespace Lax904597.Sat.satRel.negIn
end Lax904597.Sat.satRel.negIn

namespace Lax904597.Sat.satRel.posIn
end Lax904597.Sat.satRel.posIn
end

-- Lax535992.HornSat
section
namespace Lax535992
end Lax535992

namespace Lax535992.HornSat
end Lax535992.HornSat
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

-- Lax535992.LeastFixedPoint
section
namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax535992.LeastFixedPoint.Derives
end Lax535992.LeastFixedPoint.Derives

namespace Lax535992.LeastFixedPoint.LFPDef
end Lax535992.LeastFixedPoint.LFPDef
end

-- Lax535992.GameInvariance
section
namespace Lax535992.GameInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Sat Lax904597.Machines

open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms

open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure

open Lax485149.ClassNL Lax485149.ClassL

open Lax535992.HornFragment Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint

open Lax535992.HornSat Lax535992.CircuitValue Lax535992.Game Lax535992.DeterministicMachines

open Lax535992.ClassPTIME

/-- Having a winning starting position is isomorphism-invariant. -/
axiom gameWon_iso : ∀ {A B : Type} [andOrGraph.Structure A] [andOrGraph.Structure B],
  (A ≃[andOrGraph] B) → (GameWon A ↔ GameWon B)

end Lax535992.GameInvariance
end
