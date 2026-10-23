-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Set
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

-- Lax799700.Problems
section
namespace Lax799700
end Lax799700

namespace Lax799700.Problems
end Lax799700.Problems

namespace Lax799700.Problems.DecisionProblem
end Lax799700.Problems.DecisionProblem

namespace Lax799700.Problems.DecisionProblem.ofPred
end Lax799700.Problems.DecisionProblem.ofPred
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

-- Lax799700.CliqueFamily
section
namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.CliqueFamily.markedGraphRel
end Lax799700.CliqueFamily.markedGraphRel

namespace Lax799700.CliqueFamily.markedGraphRel.adj
end Lax799700.CliqueFamily.markedGraphRel.adj

namespace Lax799700.CliqueFamily.markedGraphRel.marked
end Lax799700.CliqueFamily.markedGraphRel.marked
end

-- Lax280166.CountingCliques
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingCliques
end Lax280166.CountingCliques
end

-- Lax280166.CountingDominatingSets
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingDominatingSets
end Lax280166.CountingDominatingSets
end

-- Lax799700.Feedback
section
namespace Lax799700.Feedback
end Lax799700.Feedback

namespace Lax799700.Feedback.markedArcGraphRel
end Lax799700.Feedback.markedArcGraphRel

namespace Lax799700.Feedback.markedArcGraphRel.adj
end Lax799700.Feedback.markedArcGraphRel.adj

namespace Lax799700.Feedback.markedArcGraphRel.marked
end Lax799700.Feedback.markedArcGraphRel.marked
end

-- Lax280166.CountingFeedbackSets
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingFeedbackSets
end Lax280166.CountingFeedbackSets
end

-- Lax904597.Machines
section
namespace Lax904597.Machines.Config
end Lax904597.Machines.Config

namespace Lax904597.Machines.Config.ext
end Lax904597.Machines.Config.ext

namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

variable {A : Type}

/-- A binary relation is a linear order: reflexive, transitive, antisymmetric
and total. -/
def IsLinOrd (Le : A → A → Prop) : Prop :=
  (∀ a, Le a a) ∧ (∀ a b c, Le a b → Le b c → Le a c) ∧
    (∀ a b, Le a b → Le b a → a = b) ∧ ∀ a b, Le a b ∨ Le b a

/-- A Turing machine presented as relations on a universe: the sorts, the
marks, the attributes of the transitions, the initial tape and the order along
which the head moves. -/
structure TMData (A : Type) where
  /-- Being a position – a tape cell, and equally a time step. -/
  Posn : A → Prop
  /-- The order on positions, along which the head moves. -/
  Le : A → A → Prop
  /-- Being a transition. -/
  Tr : A → Prop
  /-- Being a start state. -/
  Start : A → Prop
  /-- Being an accepting state. -/
  Acc : A → Prop
  /-- Being the blank symbol. -/
  Blank : A → Prop
  /-- This transition moves the head right (rather than left). -/
  Right : A → Prop
  /-- The state a transition applies in. -/
  Src : A → A → Prop
  /-- The symbol a transition reads. -/
  Read : A → A → Prop
  /-- The state a transition moves to. -/
  Dst : A → A → Prop
  /-- The symbol a transition writes. -/
  Write : A → A → Prop
  /-- The input: the symbol initially in a cell. -/
  Inp : A → A → Prop

namespace TMData

variable (M : TMData A)

end TMData

/-- Relation symbols of machine instances. -/
inductive turingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a tape cell, and equally a time step. -/
  | posn : turingRel 1
  /-- `tr τ`: `τ` is a transition. -/
  | tr : turingRel 1
  /-- `start q`: `q` is a start state. -/
  | start : turingRel 1
  /-- `acc q`: `q` is an accepting state. -/
  | acc : turingRel 1
  /-- `blank a`: `a` is the blank symbol. -/
  | blank : turingRel 1
  /-- `right τ`: the transition `τ` moves the head right. -/
  | right : turingRel 1
  /-- `le p q`: the linear order along which the head moves. -/
  | le : turingRel 2
  /-- `tsrc τ q`: `τ` applies in the state `q`. -/
  | tsrc : turingRel 2
  /-- `tread τ a`: `τ` applies when reading the symbol `a`. -/
  | tread : turingRel 2
  /-- `tdst τ q`: `τ` moves to the state `q`. -/
  | tdst : turingRel 2
  /-- `twrite τ a`: `τ` writes the symbol `a`. -/
  | twrite : turingRel 2
  /-- `inp p a`: the cell `p` initially holds the symbol `a`. -/
  | inp : turingRel 2
  deriving DecidableEq

/-- The relational language of machine instances: positions with their order,
transitions with their attributes, the distinguished states and symbol, and the
initial tape. -/
def turing : Language :=
  ⟨fun _ => Empty, turingRel⟩

section Shorthands

variable [turing.Structure A]

end Shorthands

end Lax904597.Machines
end

-- Lax799700.Hamilton
section
namespace Lax799700.Hamilton

open Lax904597.Machines

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive digraphRel : ℕ → Type where
/-- `arc a b`: there is an arc from `a` to `b`. -/
  | arc : digraphRel 2
  deriving DecidableEq

/-- The relational language of digraphs: one binary relation. The undirected
problem reads it symmetrically rather than on a vocabulary of its own. -/
def digraph : FirstOrder.Language :=
  ⟨fun _ => Empty, digraphRel⟩

/-- `arc a b`: there is an arc from `a` to `b`. -/
abbrev dgArc : digraph.Relations 2 :=
  .arc

open FirstOrder

open Language Structure

section Tour

variable {A : Type}

/-- `y` is the immediate `Le`-successor of `x`: above it, distinct from it,
and with nothing strictly in between. -/
def SuccOf (Le : A → A → Prop) (x y : A) : Prop :=
  Le x y ∧ x ≠ y ∧ ∀ z, Le x z → Le z y → z = x ∨ z = y

end Tour

section Problems

variable {A : Type} [digraph.Structure A]

/-- `arc a b`: there is an arc from `a` to `b`.  -/
def DGArc {A : Type} [digraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap dgArc ![a0, a1]

/-- There is an edge between `a` and `b`: the arc relation read
symmetrically, which is how the undirected problem reads its instance. -/
def DGEdge (a b : A) : Prop := DGArc a b ∨ DGArc b a

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.Hamilton
end

-- Lax280166.CountingHamiltonCircuits
section
namespace Lax280166.CountingHamiltonCircuits

open Lax799700.Hamilton Lax904597.Machines

open FirstOrder

open Language Structure

section Circuit

variable {A : Type}

/-- `y` comes next after `x` on the circuit a linear order is a cut of: it is
the immediate successor of `x`, or `x` is the last element and `y` the
first. -/
def CycSucc (Le : A → A → Prop) (x y : A) : Prop :=
  SuccOf Le x y ∨ ((∀ z, Le z x) ∧ ∀ z, Le y z)

/-- The relation `Nxt` is a Hamilton circuit of `R`: the cyclic successor
relation of a linear order of the universe, included in `R`. -/
def IsCircuit (R : A → A → Prop) (Nxt : A → A → Prop) : Prop :=
  ∃ Le : A → A → Prop, IsLinOrd Le ∧ (∀ x y, Nxt x y ↔ CycSucc Le x y) ∧
    ∀ x y, Nxt x y → R x y

end Circuit

section Problem

variable (A : Type) [digraph.Structure A]

end Problem

open FirstOrder

open Language Structure

section UCircuit

variable {A : Type}

/-- The relation `E` is the edge set of a Hamilton circuit of `R`: the
symmetric closure of a circuit of `R`. -/
def IsUCircuit (R : A → A → Prop) (E : A → A → Prop) : Prop :=
  ∃ Nxt : A → A → Prop, IsCircuit R Nxt ∧ ∀ x y, E x y ↔ (Nxt x y ∨ Nxt y x)

end UCircuit

section Problem

variable (A : Type) [digraph.Structure A]

/-- The relation `E` is the edge set of a Hamilton circuit of a finite
graph. -/
def UCircuit (E : A → A → Prop) : Prop :=
  Finite A ∧ IsUCircuit (fun x y : A => DGEdge x y) E

end Problem

open Lax366625.CountingProblems

end Lax280166.CountingHamiltonCircuits
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

-- Lax799700.Common
section
namespace Lax799700.Common
end Lax799700.Common

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc
end

-- Lax799700.Knapsack
section
namespace Lax799700.Knapsack
end Lax799700.Knapsack

namespace Lax799700.Knapsack.binWeightsRel
end Lax799700.Knapsack.binWeightsRel

namespace Lax799700.Knapsack.binWeightsRel.bit
end Lax799700.Knapsack.binWeightsRel.bit

namespace Lax799700.Knapsack.binWeightsRel.item
end Lax799700.Knapsack.binWeightsRel.item

namespace Lax799700.Knapsack.binWeightsRel.le
end Lax799700.Knapsack.binWeightsRel.le

namespace Lax799700.Knapsack.binWeightsRel.posn
end Lax799700.Knapsack.binWeightsRel.posn

namespace Lax799700.Knapsack.binWeightsRel.tgt
end Lax799700.Knapsack.binWeightsRel.tgt
end

-- Lax799700.ZeroOneIP
section
namespace Lax799700.ZeroOneIP
end Lax799700.ZeroOneIP

namespace Lax799700.ZeroOneIP.zeroOneIPRel
end Lax799700.ZeroOneIP.zeroOneIPRel

namespace Lax799700.ZeroOneIP.zeroOneIPRel.coef
end Lax799700.ZeroOneIP.zeroOneIPRel.coef

namespace Lax799700.ZeroOneIP.zeroOneIPRel.col
end Lax799700.ZeroOneIP.zeroOneIPRel.col

namespace Lax799700.ZeroOneIP.zeroOneIPRel.le
end Lax799700.ZeroOneIP.zeroOneIPRel.le

namespace Lax799700.ZeroOneIP.zeroOneIPRel.posn
end Lax799700.ZeroOneIP.zeroOneIPRel.posn

namespace Lax799700.ZeroOneIP.zeroOneIPRel.rhs
end Lax799700.ZeroOneIP.zeroOneIPRel.rhs

namespace Lax799700.ZeroOneIP.zeroOneIPRel.row
end Lax799700.ZeroOneIP.zeroOneIPRel.row
end

-- Lax280166.CountingKnapsacks
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingKnapsacks
end Lax280166.CountingKnapsacks
end

-- Lax366625.CountingSat
section
namespace Lax366625.CountingSat
end Lax366625.CountingSat
end

-- Lax799700.OneInSat
section
namespace Lax799700.OneInSat
end Lax799700.OneInSat
end

-- Lax799700.ThreeSat
section
namespace Lax799700.ThreeSat
end Lax799700.ThreeSat
end

-- Lax280166.CountingSatVariants
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingSatVariants
end Lax280166.CountingSatVariants
end

-- Lax799700.SetFamily
section
namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax799700.SetFamily.setSystemRel
end Lax799700.SetFamily.setSystemRel

namespace Lax799700.SetFamily.setSystemRel.elem
end Lax799700.SetFamily.setSystemRel.elem

namespace Lax799700.SetFamily.setSystemRel.fam
end Lax799700.SetFamily.setSystemRel.fam

namespace Lax799700.SetFamily.setSystemRel.marked
end Lax799700.SetFamily.setSystemRel.marked

namespace Lax799700.SetFamily.setSystemRel.mem
end Lax799700.SetFamily.setSystemRel.mem
end

-- Lax280166.CountingSetFamilies
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies
end

-- Lax799700.Steiner
section
namespace Lax799700.Steiner
end Lax799700.Steiner

namespace Lax799700.Steiner.steinerGraphRel
end Lax799700.Steiner.steinerGraphRel

namespace Lax799700.Steiner.steinerGraphRel.adj
end Lax799700.Steiner.steinerGraphRel.adj

namespace Lax799700.Steiner.steinerGraphRel.marked
end Lax799700.Steiner.steinerGraphRel.marked

namespace Lax799700.Steiner.steinerGraphRel.terminal
end Lax799700.Steiner.steinerGraphRel.terminal
end

-- Lax280166.CountingSteinerTrees
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingSteinerTrees
end Lax280166.CountingSteinerTrees
end

-- Lax366625.CountingClasses
section
namespace Lax366625.CountingClasses
end Lax366625.CountingClasses

namespace Lax366625.CountingClasses.CountingClass
end Lax366625.CountingClasses.CountingClass
end

-- Lax366625.WitnessCounting
section
namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting
end

-- Lax799700.DominatingSet
section
namespace Lax799700.DominatingSet
end Lax799700.DominatingSet
end

-- Lax280166.HamiltonCircuitsValues
section
namespace Lax280166.HamiltonCircuitsValues

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Sat

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat

open Lax799700.ThreeSat Lax799700.SetFamily

open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- The number counted by #Hamilton Circuit is isomorphism-invariant. -/
axiom sharpHamCircuit_count_iso :
  ∀ {A B : Type} [Lax799700.Hamilton.digraph.Structure A] [Lax799700.Hamilton.digraph.Structure B],
    (A ≃[Lax799700.Hamilton.digraph] B) → Nat.card {E : A → A → Prop // UCircuit A E} = Nat.card {E
        : B → B → Prop // UCircuit B E}

end Lax280166.HamiltonCircuitsValues
end
