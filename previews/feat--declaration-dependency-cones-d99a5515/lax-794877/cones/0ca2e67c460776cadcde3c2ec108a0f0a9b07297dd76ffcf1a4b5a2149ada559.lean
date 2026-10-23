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
import Mathlib.Data.Fin.Tuple.Basic
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
import Mathlib.Data.Nat.Log
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
import Mathlib.Order.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

-- Lax366625.CountingClasses
section
namespace Lax366625.CountingClasses
end Lax366625.CountingClasses

namespace Lax366625.CountingClasses.CountingClass
end Lax366625.CountingClasses.CountingClass
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

/-- An assignment of actual relations on a universe `A` to the relation
variables of a block. -/
def SOBlock.Assignment (B : SOBlock) (A : Type) : Type :=
  ∀ i : B.ι, (Fin (B.arity i) → A) → Prop

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
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

-- Lax535992.LeastFixedPoint
section
namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax535992.LeastFixedPoint.Derives
end Lax535992.LeastFixedPoint.Derives

namespace Lax535992.LeastFixedPoint.LFPDef
end Lax535992.LeastFixedPoint.LFPDef
end

-- Lax895169.BitPredicate
section
namespace Lax895169
end Lax895169

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax895169.BitPredicate.prefixHolds
end Lax895169.BitPredicate.prefixHolds
end

-- Lax366625.QuantitativeLogic
section
namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax366625.QuantitativeLogic.DigitLFPDef
end Lax366625.QuantitativeLogic.DigitLFPDef

namespace Lax366625.QuantitativeLogic.QLFPDef
end Lax366625.QuantitativeLogic.QLFPDef

namespace Lax366625.QuantitativeLogic.QTerm
end Lax366625.QuantitativeLogic.QTerm

namespace Lax366625.QuantitativeLogic.QTerm.add
end Lax366625.QuantitativeLogic.QTerm.add

namespace Lax366625.QuantitativeLogic.QTerm.const
end Lax366625.QuantitativeLogic.QTerm.const

namespace Lax366625.QuantitativeLogic.QTerm.eval
end Lax366625.QuantitativeLogic.QTerm.eval

namespace Lax366625.QuantitativeLogic.QTerm.ind
end Lax366625.QuantitativeLogic.QTerm.ind

namespace Lax366625.QuantitativeLogic.QTerm.mul
end Lax366625.QuantitativeLogic.QTerm.mul

namespace Lax366625.QuantitativeLogic.QTerm.prod
end Lax366625.QuantitativeLogic.QTerm.prod

namespace Lax366625.QuantitativeLogic.QTerm.sum
end Lax366625.QuantitativeLogic.QTerm.sum
end

-- Lax366625.WitnessCounting
section
namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting
end

-- Lax794877.Queries
section
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

instance instIsRelationalRst : FirstOrder.Language.IsRelational rst := fun _ =>
    (inferInstance : IsEmpty Empty)

/-- `r a`. -/
abbrev rstR : rst.Relations 1 :=
  .r

/-- `s a b`. -/
abbrev rstS : rst.Relations 2 :=
  .s

/-- `t b`. -/
abbrev rstT : rst.Relations 1 :=
  .t

open FirstOrder

open Language Structure

instance instFiniteSigmaNatRelationsRst : Finite (Σ n, rst.Relations n) :=
  Finite.of_surjective
    (fun i : Fin 3 => match i with
      | 0 => (⟨1, rstR⟩ : Σ n, rst.Relations n)
      | 1 => ⟨2, rstS⟩
      | 2 => ⟨1, rstT⟩)
    (by
      rintro ⟨n, R⟩
      cases R
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)

/-- The query `h₀ = ∃ x y, R(x) ∧ S(x, y) ∧ T(y)`. -/
noncomputable def h0 : rst.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 2)
  (FirstOrder.Language.Relations.formula₁ rstR (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
    (FirstOrder.Language.Relations.formula₂ rstS (FirstOrder.Language.Term.var (Sum.inr 0))
        (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
      FirstOrder.Language.Relations.formula₁ rstT (FirstOrder.Language.Term.var (Sum.inr 1))))

end Lax794877.Queries
end

-- Lax794877.PossibleWorlds
section
namespace Lax794877.PossibleWorlds

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-- The block guessing a world: one relation variable per relation symbol of
the schema, of the same arity. -/
def worldBlock [Finite (Σ n, L.Relations n)] : SOBlock where
  ι := Σ n, L.Relations n
  arity := fun p => p.1

section Worlds

variable {L} [Finite (Σ n, L.Relations n)] {A : Type}

/-- The structure over the schema that a family of relations is. -/
@[reducible]
def worldStructure [L.IsRelational] (ρ : (worldBlock L).Assignment A) : L.Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {n} R x => ρ ⟨n, R⟩ x

end Worlds

open Lax366625.CountingProblems

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

/-- Probability of a single valuation `v : X → Bool`, under the independence
assumption: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`. -/
def valProb (v : X → Bool) : ℚ :=
  ∏ x, if v x then P.prob x else 1 - P.prob x

/-- Probability of an event, a Boolean function of the valuation:
`Pr(f) = ∑_{v ⊨ f} Pr(v)`. -/
def funcProb (f : (X → Bool) → Bool) : ℚ :=
  ∑ v : X → Bool, if f v then P.valProb v else 0

end ProbAssignment

section Weights

variable (a c : X → ℕ)

/-- The probability assignment of a family of weights: the variable `x` is
true with probability `a x / (a x + c x)`. -/
def ProbAssignment.ofWeights (h : ∀ x, 0 < a x + c x) : ProbAssignment X where
  prob x := (a x : ℚ) / ((a x : ℚ) + c x)
  prob_nonneg x := div_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _))
  prob_le_one x := by
    have hpos : (0 : ℚ) < (a x : ℚ) + c x := by exact_mod_cast h x
    rw [div_le_one hpos]
    have : (0 : ℚ) ≤ c x := Nat.cast_nonneg _
    linarith

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

instance (L : Language.{0, 0}) : (weightedLang L).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

variable {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)]

section Kernel

variable {A : Type} [(weightedLang L).Structure A]

/-- The bits of a weight of a fact, read through a symbol of arity one more
than the fact's. -/
def bitsOf {n : ℕ} (S : WeightedRel L (n + 1)) (x : Fin n → A) : A → Prop :=
  fun i => RelMap (L := weightedLang L) S (Fin.snoc (α := fun _ => A) x i)

/-- The order of the positions of a weighted instance. -/
def WLe (L : Language.{0, 0}) (A : Type) [(weightedLang L).Structure A] (a b : A) : Prop :=
  RelMap (L := weightedLang L) WeightedRel.le ![a, b]

end Kernel

section Count

variable [L.IsRelational] {A : Type} [(weightedLang L).Structure A]

/-- The facts over a universe: a symbol of the schema and a tuple. -/
abbrev Fact (L : Language.{0, 0}) (A : Type) : Type := Σ p : Σ n, L.Relations n, Fin p.1 → A

/-- The fact is open: uncertain and not certain. -/
def IsOpen (q : Fact L A) : Prop :=
  RelMap (L := weightedLang L) (WeightedRel.unc q.1.2) q.2 ∧
    ¬RelMap (L := weightedLang L) (WeightedRel.cert q.1.2) q.2

/-- The open facts of a finite instance, as a finite type: the independent
Boolean variables of the instance. -/
noncomputable instance openFactFintype [Finite A] : Fintype {q : Fact L A // IsOpen q} :=
  Fintype.ofFinite _

/-- The weight of presence of an open fact. -/
noncomputable def presWeight (x : {q : Fact L A // IsOpen q}) : ℕ :=
  binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.pres x.1.1.2) x.1.2)

/-- The weight of absence of an open fact. -/
noncomputable def absWeight (x : {q : Fact L A // IsOpen q}) : ℕ :=
  binNum (WLe L A) (fun _ => True) (bitsOf (WeightedRel.abs x.1.1.2) x.1.2)

/-- The world of a valuation of the open facts: the certain facts, and the
open facts the valuation makes true. -/
def worldOfVal (v : {q : Fact L A // IsOpen q} → Bool) : (worldBlock L).Assignment A :=
  fun p x => RelMap (L := weightedLang L) (WeightedRel.cert p.2) x ∨
    ∃ h : IsOpen (⟨p, x⟩ : Fact L A), v ⟨⟨p, x⟩, h⟩ = true

open Classical in
/-- The event “the sentence holds in the world”, as a Boolean function of the
valuation of the open facts. -/
noncomputable def holdsEvent (φ : L.Sentence) (v : {q : Fact L A // IsOpen q} → Bool) : Bool :=
  decide (@Sentence.Realize L A (worldStructure (worldOfVal v)) φ)

open Classical in
/-- **The probability of a sentence** over a weighted instance: each open fact
is present independently, with probability its weight of presence over the sum
of its two weights, and the probability is that of the event that the sentence
holds in the resulting world. -/
noncomputable def worldProb [Finite A] (φ : L.Sentence)
    (hpos : ∀ x : {q : Fact L A // IsOpen q}, 0 < presWeight x + absWeight x) : ℚ :=
  (ProbAssignment.ofWeights presWeight absWeight hpos).funcProb (holdsEvent φ)

end Count

open Lax366625.CountingProblems Lax904597.Machines

end Lax794877.WeightedWorlds
end

-- Lax794877.ExampleDatabase
section
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

/-- A world may give the fact the truth value `b`: an absent fact is false, a
certain fact is true, an uncertain fact is either. -/
def admits : FactStatus → Bool → Bool
  | absent, b => !b
  | certain, b => b
  | uncertain _ _, _ => true

/-- The weight the fact contributes to a world giving it the truth value `b`:
its weight of presence or of absence if it is uncertain, and `1` otherwise. -/
def weight : FactStatus → Bool → ℕ
  | uncertain a c, b => if b then a else c
  | _, _ => 1

end FactStatus

/-- A world over `n` constants: the truth value of every possible fact. -/
abbrev World (n : ℕ) : Type := (Fin n → Bool) × (Fin n → Fin n → Bool) × (Fin n → Bool)

namespace ProbDb

variable (i : ProbDb)

/-- The world is a possible world of the database. -/
def Valid (W : World i.n) : Prop :=
  (∀ x, (i.r x).admits (W.1 x) = true) ∧ (∀ x y, (i.s x y).admits (W.2.1 x y) = true) ∧
    ∀ y, (i.t y).admits (W.2.2 y) = true

instance instDecidableValid (W : World i.n) : Decidable (i.Valid W) := by
  unfold Valid
  infer_instance

/-- The weight of a world: the product of the weights of the facts. -/
def weight (W : World i.n) : ℕ :=
  (∏ x, (i.r x).weight (W.1 x)) * ((∏ x, ∏ y, (i.s x y).weight (W.2.1 x y)) *
    ∏ y, (i.t y).weight (W.2.2 y))

end ProbDb

/-- The query `h₀` holds in a world. -/
def HoldsH0 {n : ℕ} (W : World n) : Prop :=
  ∃ x y, W.1 x = true ∧ W.2.1 x y = true ∧ W.2.2 y = true

instance {n : ℕ} (W : World n) : Decidable (HoldsH0 W) := by
  unfold HoldsH0
  infer_instance

/-- **The concrete weighted count of `h₀`**: the sum of the weights of the
possible worlds of the database in which the query holds. -/
def ProbDb.count (i : ProbDb) : ℕ :=
  ∑ W : World i.n, if i.Valid W ∧ HoldsH0 W then i.weight W else 0

/-- The weighted count of all the possible worlds: the denominator of the
probability. -/
def ProbDb.total (i : ProbDb) : ℕ :=
  ∑ W : World i.n, if i.Valid W then i.weight W else 0

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

/-- **The encoded database**: the weighted instance on the constants. -/
def probDbStructure (i : ProbDb) : (weightedLang rst).Structure (Fin i.n) where
  funMap f := isEmptyElim f
  RelMap R x := probDbRel i R x = true

end Lax794877.ExampleDatabase
end

-- Lax859101.OneCallReductions
section
namespace Lax859101
end Lax859101

namespace Lax859101.OneCallReductions
end Lax859101.OneCallReductions

namespace Lax859101.OneCallReductions.OneCallReduction
end Lax859101.OneCallReductions.OneCallReduction

namespace Lax859101.OneCallReductions.PolyTerm
end Lax859101.OneCallReductions.PolyTerm

namespace Lax859101.OneCallReductions.PostTerm
end Lax859101.OneCallReductions.PostTerm

namespace Lax859101.OneCallReductions.PolyTerm.add
end Lax859101.OneCallReductions.PolyTerm.add

namespace Lax859101.OneCallReductions.PolyTerm.card
end Lax859101.OneCallReductions.PolyTerm.card

namespace Lax859101.OneCallReductions.PolyTerm.eval
end Lax859101.OneCallReductions.PolyTerm.eval

namespace Lax859101.OneCallReductions.PolyTerm.mul
end Lax859101.OneCallReductions.PolyTerm.mul

namespace Lax859101.OneCallReductions.PolyTerm.num
end Lax859101.OneCallReductions.PolyTerm.num

namespace Lax859101.OneCallReductions.PostTerm.add
end Lax859101.OneCallReductions.PostTerm.add

namespace Lax859101.OneCallReductions.PostTerm.div
end Lax859101.OneCallReductions.PostTerm.div

namespace Lax859101.OneCallReductions.PostTerm.eval
end Lax859101.OneCallReductions.PostTerm.eval

namespace Lax859101.OneCallReductions.PostTerm.mod
end Lax859101.OneCallReductions.PostTerm.mod

namespace Lax859101.OneCallReductions.PostTerm.mul
end Lax859101.OneCallReductions.PostTerm.mul

namespace Lax859101.OneCallReductions.PostTerm.oracle
end Lax859101.OneCallReductions.PostTerm.oracle

namespace Lax859101.OneCallReductions.PostTerm.poly
end Lax859101.OneCallReductions.PostTerm.poly

namespace Lax859101.OneCallReductions.PostTerm.pow2
end Lax859101.OneCallReductions.PostTerm.pow2

namespace Lax859101.OneCallReductions.PostTerm.sub
end Lax859101.OneCallReductions.PostTerm.sub
end

-- Lax794877.ExampleDatabaseProbability
section
namespace Lax794877.ExampleDatabaseProbability

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

open Lax794877.PossibleWorlds Lax799700.Common Lax904597.SecondOrder

open FirstOrder.Language

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.QuantitativeLogic

open Lax859101.OneCallReductions Lax904597.Machines

open Lax794877.PossibleWorlds Lax794877.WeightedWorlds Lax794877.Queries Lax794877.ExampleDatabase

/-- The probability of h₀ over a database is its count divided by its total. -/
axiom probDb_worldProb_eq :
  ∀ (i : ProbDb) (hpos : ∀ x : {q : @Fact rst (Fin i.n) // @IsOpen _ _ (probDbStructure i) q},
      0 < @presWeight _ _ (probDbStructure i) x + @absWeight _ _ (probDbStructure i) x),
    @worldProb _ _ _ _ (probDbStructure i) _ h0 hpos = (i.count : ℚ) / (i.total : ℚ)

end Lax794877.ExampleDatabaseProbability
end
