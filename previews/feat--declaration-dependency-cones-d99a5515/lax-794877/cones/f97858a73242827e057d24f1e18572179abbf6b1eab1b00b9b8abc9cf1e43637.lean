-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Hom.Set
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- Lax794877.Queries
section
namespace Lax794877.Queries.instFiniteSigmaNatRelationsRst
end Lax794877.Queries.instFiniteSigmaNatRelationsRst

namespace Lax794877.Queries

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive rstRel : ℕ → Type where
/-- `r a`. -/
  | r : rstRel 1
/-- `s a b`. -/
  | s : rstRel 2
/-- `t b`. -/
  | t : rstRel 1
  deriving DecidableEq

/-- The schema of the example: two unary relations and a binary one. -/
def rst : FirstOrder.Language :=
  ⟨fun _ => Empty, rstRel⟩

open FirstOrder

open Language Structure

end Lax794877.Queries
end

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

-- Lax794877.PossibleWorlds
section
namespace Lax794877
end Lax794877

namespace Lax794877.PossibleWorlds
end Lax794877.PossibleWorlds
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

-- Lax794877.WeightedWorlds
section
namespace Lax794877.WeightedWorlds

open Lax794877.PossibleWorlds Lax799700.Common Lax904597.SecondOrder

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A probability assignment to a finite set `X` of Boolean variables: each
variable is assigned a rational probability in `[0, 1]`. -/
structure ProbAssignment (X : Type) where
  /-- The probability assigned to each variable. -/
  prob : X → ℚ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ x, 0 ≤ prob x
  /-- Probabilities are at most `1`. -/
  prob_le_one : ∀ x, prob x ≤ 1

namespace ProbAssignment

variable (P : ProbAssignment X)

end ProbAssignment

section Weights

variable (a c : X → ℕ)

end Weights

open FirstOrder

open Language Structure

/-- The relation symbols of a weighted instance over the schema `L`: for each
symbol of the schema, the certain facts, the uncertain facts, and the bits of
the two weights of each fact; and one order, on the bit positions. -/
inductive WeightedRel (L : Language.{0, 0}) : ℕ → Type
  /-- The certain facts. -/
  | cert {n : ℕ} (R : L.Relations n) : WeightedRel L n
  /-- The uncertain facts. -/
  | unc {n : ℕ} (R : L.Relations n) : WeightedRel L n
  /-- `pres R (x̄, i)`: the bit of position `i` of the weight of the fact `R(x̄)`
  being present. -/
  | pres {n : ℕ} (R : L.Relations n) : WeightedRel L (n + 1)
  /-- `abs R (x̄, i)`: the bit of position `i` of the weight of the fact `R(x̄)`
  being absent. -/
  | abs {n : ℕ} (R : L.Relations n) : WeightedRel L (n + 1)
  /-- The order of the bit positions. -/
  | le : WeightedRel L 2

/-- The vocabulary of weighted instances over the schema `L`. -/
def weightedLang (L : Language.{0, 0}) : Language.{0, 0} :=
  ⟨fun _ => Empty, WeightedRel L⟩

variable {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)]

section Kernel

variable {A : Type} [(weightedLang L).Structure A]

end Kernel

section Count

variable [L.IsRelational] {A : Type} [(weightedLang L).Structure A]

end Count

open Lax366625.CountingProblems Lax904597.Machines

end Lax794877.WeightedWorlds
end

-- Lax794877.ExampleDatabase
section
namespace Lax794877.ExampleDatabase.FactStatus.admits
end Lax794877.ExampleDatabase.FactStatus.admits

namespace Lax794877.ExampleDatabase.FactStatus.weight
end Lax794877.ExampleDatabase.FactStatus.weight

namespace Lax794877.ExampleDatabase

open FirstOrder

open Language Structure

/-- What a database says of a fact: it is absent, it is certain, or it is
uncertain with weights `a` and `c`, i.e., present with probability
`a / (a + c)`. -/
inductive FactStatus : Type
  /-- The fact is not in the database. -/
  | absent : FactStatus
  /-- The fact is in the database for sure. -/
  | certain : FactStatus
  /-- The fact is present with weight `a` and absent with weight `c`. -/
  | uncertain (a c : ℕ) : FactStatus
  deriving DecidableEq

namespace FactStatus

/-- The fact is certain. -/
def isCert : FactStatus → Bool
  | certain => true
  | _ => false

/-- The fact is uncertain. -/
def isUnc : FactStatus → Bool
  | uncertain _ _ => true
  | _ => false

/-- The weight of presence of an uncertain fact (and `0` otherwise). -/
def presW : FactStatus → ℕ
  | uncertain a _ => a
  | _ => 0

/-- The weight of absence of an uncertain fact (and `0` otherwise). -/
def absW : FactStatus → ℕ
  | uncertain _ c => c
  | _ => 0

end FactStatus

/-- **A probabilistic database** over the schema `R`, `S`, `T`, with `n`
constants: the status of every possible fact. The weights are written in
binary on `n` bits, so they are below `2 ^ n`. -/
structure ProbDb where
  /-- The number of constants. -/
  n : ℕ
  /-- The status of the fact `R(x)`. -/
  r : Fin n → FactStatus
  /-- The status of the fact `S(x, y)`. -/
  s : Fin n → Fin n → FactStatus
  /-- The status of the fact `T(y)`. -/
  t : Fin n → FactStatus
  /-- The weights of the `R`-facts fit in `n` bits. -/
  fits_r : ∀ x, (r x).presW < 2 ^ n ∧ (r x).absW < 2 ^ n
  /-- The weights of the `S`-facts fit in `n` bits. -/
  fits_s : ∀ x y, (s x y).presW < 2 ^ n ∧ (s x y).absW < 2 ^ n
  /-- The weights of the `T`-facts fit in `n` bits. -/
  fits_t : ∀ y, (t y).presW < 2 ^ n ∧ (t y).absW < 2 ^ n

namespace FactStatus

end FactStatus

namespace ProbDb

variable (i : ProbDb)

end ProbDb

open Lax794877.WeightedWorlds Lax794877.Queries

/-- The relations of the encoded database: the status of each fact, the binary
digits of its weights, and the order of the constants. -/
def probDbRel (i : ProbDb) : ∀ {n}, (weightedLang rst).Relations n → (Fin n → Fin i.n) → Bool :=
  fun {n} R =>
    match n, R with
    | _, .cert .r => fun x => (i.r (x 0)).isCert
    | _, .cert .s => fun x => (i.s (x 0) (x 1)).isCert
    | _, .cert .t => fun x => (i.t (x 0)).isCert
    | _, .unc .r => fun x => (i.r (x 0)).isUnc
    | _, .unc .s => fun x => (i.s (x 0) (x 1)).isUnc
    | _, .unc .t => fun x => (i.t (x 0)).isUnc
    | _, .pres .r => fun x => (i.r (x 0)).presW.testBit (x 1).1
    | _, .pres .s => fun x => (i.s (x 0) (x 1)).presW.testBit (x 2).1
    | _, .pres .t => fun x => (i.t (x 0)).presW.testBit (x 1).1
    | _, .abs .r => fun x => (i.r (x 0)).absW.testBit (x 1).1
    | _, .abs .s => fun x => (i.s (x 0) (x 1)).absW.testBit (x 2).1
    | _, .abs .t => fun x => (i.t (x 0)).absW.testBit (x 1).1
    | _, .le => fun x => decide (x 0 ≤ x 1)

end Lax794877.ExampleDatabase
end
