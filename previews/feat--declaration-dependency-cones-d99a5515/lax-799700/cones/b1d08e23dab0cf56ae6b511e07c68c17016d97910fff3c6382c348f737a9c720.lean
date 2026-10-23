-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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

end Lax904597.Sat
end

-- Lax799700.Common
section
namespace Lax799700.Common

open Lax904597.Sat

section Decode

variable {A : Type}

/-- The rank of a position: the number of positions strictly below it. This is
the place value's exponent. -/
noncomputable def bitRank (Le : A → A → Prop) (Posn : A → Prop) (p : A) : ℕ :=
  ({q | Posn q ∧ Le q p ∧ q ≠ p} : Set A).ncard

/-- The number encoded by the set `b` of positions: `∑ 2 ^ rank`. -/
noncomputable def binNum (Le : A → A → Prop) (Posn b : A → Prop) : ℕ :=
  ∑ᶠ p ∈ {p | Posn p ∧ b p}, 2 ^ bitRank Le Posn p

end Decode

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [sat.Structure A]

end SatOcc

end Lax799700.Common
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

-- Lax799700.Knapsack
section
namespace Lax799700.Knapsack

open Lax799700.Common Lax904597.Machines

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive binWeightsRel : ℕ → Type where
/-- `item i`: `i` is an item. -/
  | item : binWeightsRel 1
/-- `posn p`: `p` is a bit position. -/
  | posn : binWeightsRel 1
/-- `bit i p`: the weight of `i` has bit 1 at position `p`. -/
  | bit : binWeightsRel 2
/-- `tgt p`: the target has bit 1 at position `p`. -/
  | tgt : binWeightsRel 1
/-- `le a b`: the linear order carrying the place values. -/
  | le : binWeightsRel 2
  deriving DecidableEq

/-- The relational language of binary-weighted instances: items and bit
positions, the bits of each item's weight and of the target, and a linear
order. -/
def binWeights : FirstOrder.Language :=
  ⟨fun _ => Empty, binWeightsRel⟩

/-- `posn p`: `p` is a bit position. -/
abbrev bwPosn : binWeights.Relations 1 :=
  .posn

/-- `bit i p`: the weight of `i` has bit 1 at position `p`. -/
abbrev bwBit : binWeights.Relations 2 :=
  .bit

/-- `le a b`: the linear order carrying the place values. -/
abbrev bwLe : binWeights.Relations 2 :=
  .le

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [binWeights.Structure A]

/-- `posn p`: `p` is a bit position.  -/
def BWPosn {A : Type} [binWeights.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwPosn ![a0]

/-- `bit i p`: the weight of `i` has bit 1 at position `p`.  -/
def BWBit {A : Type} [binWeights.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwBit ![a0, a1]

/-- `le a b`: the linear order carrying the place values.  -/
def BWLe {A : Type} [binWeights.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwLe ![a0, a1]

/-- The weight of an item, decoded. -/
noncomputable def BWWeight (i : A) : ℕ := binNum BWLe BWPosn (BWBit i)

end Shorthands

section Problem

variable (A : Type) [binWeights.Structure A]

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.Knapsack
end
