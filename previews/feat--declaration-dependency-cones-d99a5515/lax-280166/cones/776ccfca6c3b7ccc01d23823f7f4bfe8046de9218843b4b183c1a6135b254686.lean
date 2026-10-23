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

-- Lax799700.Hamilton
section
namespace Lax799700.Hamilton
end Lax799700.Hamilton

namespace Lax799700.Hamilton.digraphRel
end Lax799700.Hamilton.digraphRel

namespace Lax799700.Hamilton.digraphRel.arc
end Lax799700.Hamilton.digraphRel.arc
end

-- Lax280166.CountingHamiltonCircuits
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingHamiltonCircuits
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

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive steinerGraphRel : ℕ → Type where
/-- `adj a b`: there is an edge between `a` and `b`. -/
  | adj : steinerGraphRel 2
/-- `terminal a`: the vertex `a` must be spanned. -/
  | terminal : steinerGraphRel 1
/-- `marked a`: the vertex `a` belongs to the marked set carrying the
  threshold. -/
  | marked : steinerGraphRel 1
  deriving DecidableEq

/-- The relational language of graphs with terminals: adjacency, a set of
terminals to be spanned, and a marked set whose cardinality is the budget of
non-terminals. -/
def steinerGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, steinerGraphRel⟩

/-- `adj a b`: there is an edge between `a` and `b`. -/
abbrev stAdj : steinerGraph.Relations 2 :=
  .adj

/-- `terminal a`: the vertex `a` must be spanned. -/
abbrev stTerminal : steinerGraph.Relations 1 :=
  .terminal

/-- `marked a`: the vertex `a` belongs to the marked set carrying the
  threshold. -/
abbrev stMarked : steinerGraph.Relations 1 :=
  .marked

open FirstOrder

open Language Structure

section Connectivity

variable {A : Type}

/-- The edges available inside a chosen set: adjacency in either direction,
restricted to the set. -/
def Link (Adjp : A → A → Prop) (S : A → Prop) (a b : A) : Prop :=
  S a ∧ S b ∧ (Adjp a b ∨ Adjp b a)

/-- A set of vertices is connected if any two of its members are joined by a
path inside it. -/
def ConnectedOn (Adjp : A → A → Prop) (S : A → Prop) : Prop :=
  ∀ x y, S x → S y → Relation.ReflTransGen (Link Adjp S) x y

end Connectivity

section Generic

variable {A : Type}

variable {B : Type}

end Generic

section Problem

section Shorthands

variable {A : Type} [steinerGraph.Structure A]

/-- `adj a b`: there is an edge between `a` and `b`.  -/
def STAdj {A : Type} [steinerGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap stAdj ![a0, a1]

/-- `terminal a`: the vertex `a` must be spanned.  -/
def STTerminal {A : Type} [steinerGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap stTerminal ![a0]

/-- `marked a`: the vertex `a` belongs to the marked set carrying the
threshold.  -/
def STMarked {A : Type} [steinerGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap stMarked ![a0]

end Shorthands

variable (A : Type) [steinerGraph.Structure A]

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.Steiner
end

-- Lax280166.CountingSteinerTrees
section
namespace Lax280166.CountingSteinerTrees

open Lax799700.Steiner

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The set `S` contains every terminal, is connected, and has exactly as many
non-terminals as the `Kp`-marked set has elements. -/
def SteinerOfSizeOn (Adjp : A → A → Prop) (Term Kp : A → Prop) (S : A → Prop) : Prop :=
  (∀ x, Term x → S x) ∧ ConnectedOn Adjp S ∧
    {x | S x ∧ ¬Term x}.ncard = {x | Kp x}.ncard

end Generic

section Problem

variable (A : Type) [steinerGraph.Structure A]

/-- The set `S` is a connected set containing every terminal and using exactly
as many non-terminals as the marked set has elements, in a finite graph. -/
def SteinerOfSize (S : A → Prop) : Prop :=
  Finite A ∧ SteinerOfSizeOn (fun a b : A => STAdj a b) (fun a => STTerminal a)
    (fun a => STMarked a) S

end Problem

open Lax366625.CountingProblems

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

-- Lax280166.SteinerTreesValues
section
namespace Lax280166.SteinerTreesValues

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Sat

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat

open Lax799700.ThreeSat Lax799700.SetFamily

open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- The number counted by #Steiner Tree is isomorphism-invariant. -/
axiom sharpSteinerTree_count_iso :
  ∀ {A B : Type} [Lax799700.Steiner.steinerGraph.Structure A]
      [Lax799700.Steiner.steinerGraph.Structure B],
    (A ≃[Lax799700.Steiner.steinerGraph] B) → Nat.card {S : A → Prop // SteinerOfSize A S} =
        Nat.card {S : B → Prop // SteinerOfSize B S}

end Lax280166.SteinerTreesValues
end
