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
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
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

instance instIsRelationalBinWeights : FirstOrder.Language.IsRelational binWeights := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `item i`: `i` is an item. -/
abbrev bwItem : binWeights.Relations 1 :=
  .item

/-- `posn p`: `p` is a bit position. -/
abbrev bwPosn : binWeights.Relations 1 :=
  .posn

/-- `bit i p`: the weight of `i` has bit 1 at position `p`. -/
abbrev bwBit : binWeights.Relations 2 :=
  .bit

/-- `tgt p`: the target has bit 1 at position `p`. -/
abbrev bwTgt : binWeights.Relations 1 :=
  .tgt

/-- `le a b`: the linear order carrying the place values. -/
abbrev bwLe : binWeights.Relations 2 :=
  .le

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [binWeights.Structure A]

/-- `item i`: `i` is an item.  -/
def BWItem {A : Type} [binWeights.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwItem ![a0]

/-- `posn p`: `p` is a bit position.  -/
def BWPosn {A : Type} [binWeights.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwPosn ![a0]

/-- `bit i p`: the weight of `i` has bit 1 at position `p`.  -/
def BWBit {A : Type} [binWeights.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwBit ![a0, a1]

/-- `tgt p`: the target has bit 1 at position `p`.  -/
def BWTgt {A : Type} [binWeights.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwTgt ![a0]

/-- `le a b`: the linear order carrying the place values.  -/
def BWLe {A : Type} [binWeights.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bwLe ![a0, a1]

/-- The weight of an item, decoded. -/
noncomputable def BWWeight (i : A) : ℕ := binNum BWLe BWPosn (BWBit i)

end Shorthands

/-- The target of a binary-weighted instance, decoded. -/
noncomputable def BWTarget (A : Type) [binWeights.Structure A] : ℕ :=
  binNum (BWLe (A := A)) BWPosn BWTgt

section Problem

variable (A : Type) [binWeights.Structure A]

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.Knapsack
end

-- Lax799700.ZeroOneIP
section
namespace Lax799700.ZeroOneIP

open Lax799700.Common Lax904597.Machines

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive zeroOneIPRel : ℕ → Type where
/-- `col j`: `j` is a column, that is, a `0-1` variable. -/
  | col : zeroOneIPRel 1
/-- `row r`: `r` is a row, that is, an equation. -/
  | row : zeroOneIPRel 1
/-- `posn p`: `p` is a bit position. -/
  | posn : zeroOneIPRel 1
/-- `coef r j p`: the entry of row `r` in column `j` has bit 1 at `p`. -/
  | coef : zeroOneIPRel 3
/-- `rhs r p`: the right-hand side of row `r` has bit 1 at `p`. -/
  | rhs : zeroOneIPRel 2
/-- `le a b`: the linear order carrying the place values. -/
  | le : zeroOneIPRel 2
  deriving DecidableEq

/-- The relational language of 0-1 integer programs: columns, rows and bit
positions, the bits of each entry and of each right-hand side, and a linear
order. -/
def zeroOneIP : FirstOrder.Language :=
  ⟨fun _ => Empty, zeroOneIPRel⟩

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [zeroOneIP.Structure A]

end Shorthands

section Problem

variable (A : Type) [zeroOneIP.Structure A]

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.ZeroOneIP
end

-- Lax280166.CountingKnapsacks
section
namespace Lax280166.CountingKnapsacks

open Lax799700.Knapsack Lax799700.ZeroOneIP Lax904597.Machines

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [binWeights.Structure A]

/-- The set `S` of items is a solution: the instance is finite, its order is
linear, and the weights of `S` sum exactly to the target. -/
def KnapsackSol (S : A → Prop) : Prop :=
  Finite A ∧ IsLinOrd (BWLe (A := A)) ∧ (∀ i, S i → BWItem i) ∧
    (∑ᶠ i ∈ {i | S i}, BWWeight i) = BWTarget A

open FirstOrder

open Language Structure

variable (A : Type) [zeroOneIP.Structure A]

end Solutions

open Lax366625.CountingProblems

/-- **#Knapsack**, as a counting problem. -/
noncomputable def SharpKnapsack : CountingProblem Lax799700.Knapsack.binWeights :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // KnapsackSol A S}

end Lax280166.CountingKnapsacks
end
