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
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

instance instCoeFun : CoeFun (DecisionProblem L) fun _ => ∀ (A : Type) [L.Structure A], Prop :=
  ⟨Holds⟩

end DecisionProblem

end Lax904597.Problems
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

/-- The universe of the structure interpreted in `A`: tagged `dim`-tuples. -/
protected def Map (_I : FOInterpretation L L' Tag dim) (A : Type) : Type :=
  Tag × (Fin dim → A)

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The `L'`-structure interpreted in the `L`-structure `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2

end FOInterpretation

section Ordered

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [LE A]

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

instance sumOrderOrderedStructure : (L.sum Language.order).OrderedStructure A :=
  ⟨fun _ => Iff.rfl⟩

end Ordered

end Lax904597.Interpretations
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction

namespace Lax904597.Relativized

open FirstOrder FirstOrder.Language Lax904597.Problems Lax904597.Interpretations

/-- A relativized interpretation: an interpretation together with the domain
formula of each tag. -/
structure RelFOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ)
    extends FOInterpretation L L' Tag dim where
  /-- The domain formula of each tag: a tagged tuple `(t, ā)` belongs to the
  target universe iff `domFormula t` holds of `ā`. -/
  domFormula : Tag → L.Formula (Fin dim)

namespace RelFOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The universe of the relativized interpretation in `A`: the tagged tuples
whose coordinates satisfy their tag's domain formula. -/
protected def MapRel : Type :=
  {x : Tag × (Fin dim → A) // (I.domFormula x.1).Realize x.2}

/-- The `L'`-structure interpreted on the definable subset. -/
instance mapRelStructure [L'.IsRelational] : L'.Structure (I.MapRel A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1.1).Realize fun p => (xs p.1).1.2 p.2

end RelFOInterpretation

end Lax904597.Relativized
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

instance instCoeFun : CoeFun (CountingProblem L) fun _ => ∀ (A : Type) [L.Structure A], ℕ :=
  ⟨Count⟩

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

/-- The relational vocabulary of a block: one relation symbol per relation
variable. -/
def SOBlock.lang (B : SOBlock) : Language :=
  ⟨fun _ => Empty, fun n => {i : B.ι // B.arity i = n}⟩

instance instIsRelationalLang (B : SOBlock) : IsRelational B.lang :=
  fun _ => ⟨fun f => Empty.elim f⟩

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

instance instIsRelationalSat : IsRelational sat := fun _ => (inferInstance : IsEmpty Empty)

end Lax904597.Sat
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

instance instIsRelationalTuring : IsRelational turing := fun _ => (inferInstance : IsEmpty Empty)

section Shorthands

variable [turing.Structure A]

end Shorthands

end Lax904597.Machines
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

instance (L : Language.{0, 0}) : (weightedLang L).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

variable {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)]

/-- The block guessing a weighted world: a world, and for each fact a number,
as the set of its bits. -/
def weightBlock (L : Language.{0, 0}) [Finite (Σ n, L.Relations n)] : SOBlock where
  ι := (Σ n, L.Relations n) ⊕ (Σ n, L.Relations n)
  arity := Sum.elim (fun p => p.1) fun p => p.1 + 1

section Kernel

variable {A : Type} [(weightedLang L).Structure A]

/-- The world of an assignment of the block. -/
def worldOf (σ : (weightBlock L).Assignment A) : (worldBlock L).Assignment A :=
  fun p x => σ (Sum.inl p) x

/-- The number an assignment of the block attaches to a fact, as its set of
bits. -/
def numOf (σ : (weightBlock L).Assignment A) (p : Σ n, L.Relations n) (x : Fin p.1 → A) :
    A → Prop :=
  fun i => σ (Sum.inr p) (Fin.snoc (α := fun _ => A) x i)

/-- The bits of a weight of a fact, read through a symbol of arity one more
than the fact's. -/
def bitsOf {n : ℕ} (S : WeightedRel L (n + 1)) (x : Fin n → A) : A → Prop :=
  fun i => RelMap (L := weightedLang L) S (Fin.snoc (α := fun _ => A) x i)

/-- The order of the positions of a weighted instance. -/
def WLe (L : Language.{0, 0}) (A : Type) [(weightedLang L).Structure A] (a b : A) : Prop :=
  RelMap (L := weightedLang L) WeightedRel.le ![a, b]

/-- One set of bits is below another, by the highest position at which they
differ. -/
def BitLt (Le : A → A → Prop) (b w : A → Prop) : Prop :=
  ∃ i, w i ∧ ¬b i ∧ ∀ j, Le i j → j ≠ i → (b j ↔ w j)

/-- What the kernel asks of an assignment at one fact: the world keeps a
certain fact and contains only certain or uncertain ones; at an *open* fact –
uncertain and not certain – the number is below the weight of presence if the
world keeps the fact, and below the weight of absence if not; at any other
fact the number is zero. -/
def WeightCond (σ : (weightBlock L).Assignment A) (p : Σ n, L.Relations n)
    (x : Fin p.1 → A) : Prop :=
  ((RelMap (L := weightedLang L) (WeightedRel.cert p.2) x → worldOf σ p x) ∧
      (worldOf σ p x → RelMap (L := weightedLang L) (WeightedRel.cert p.2) x ∨
        RelMap (L := weightedLang L) (WeightedRel.unc p.2) x)) ∧
    ((RelMap (L := weightedLang L) (WeightedRel.unc p.2) x ∧
          ¬RelMap (L := weightedLang L) (WeightedRel.cert p.2) x →
        (worldOf σ p x →
            BitLt (WLe L A) (numOf σ p x) (bitsOf (WeightedRel.pres p.2) x)) ∧
          (¬worldOf σ p x →
            BitLt (WLe L A) (numOf σ p x) (bitsOf (WeightedRel.abs p.2) x))) ∧
      (¬(RelMap (L := weightedLang L) (WeightedRel.unc p.2) x ∧
          ¬RelMap (L := weightedLang L) (WeightedRel.cert p.2) x) →
        ∀ i, ¬numOf σ p x i))

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

end Count

open Lax366625.CountingProblems Lax904597.Machines

/-- **Counting weighted possible worlds**: the witnesses are the worlds in which
the sentence `φ` holds, each with one number per open fact below the weight
that fact takes in the world. -/
noncomputable def WeightedWorlds {L : Language.{0, 0}} [Finite
    (Σ n, L.Relations n)] [L.IsRelational]
    (φ : L.Sentence) : CountingProblem (weightedLang L) :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {σ : (weightBlock L).Assignment A // IsLinOrd (WLe L A) ∧
      (∀ (p : Σ n, L.Relations n) (x : Fin p.1 → A), WeightCond σ p x) ∧
      @Sentence.Realize L A (worldStructure (worldOf σ)) φ}

end Lax794877.WeightedWorlds
end

-- Lax794877.ExampleDatabase
section
namespace Lax794877.ExampleDatabase.probDbRel
end Lax794877.ExampleDatabase.probDbRel

namespace Lax794877.ExampleDatabase.FactStatus.isCert
end Lax794877.ExampleDatabase.FactStatus.isCert

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

end ProbDb

/-- The query `h₀` holds in a world. -/
def HoldsH0 {n : ℕ} (W : World n) : Prop :=
  ∃ x y, W.1 x = true ∧ W.2.1 x y = true ∧ W.2.2 y = true

instance {n : ℕ} (W : World n) : Decidable (HoldsH0 W) := by
  unfold HoldsH0
  infer_instance

open Lax794877.WeightedWorlds Lax794877.Queries

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

-- Lax794877.ProbabilityRatio
section
namespace Lax794877.ProbabilityRatio

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

open Lax794877.PossibleWorlds Lax799700.Common Lax904597.SecondOrder

open FirstOrder.Language

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.QuantitativeLogic

open Lax859101.OneCallReductions Lax904597.Machines

open Lax794877.PossibleWorlds Lax794877.WeightedWorlds Lax794877.Queries Lax794877.ExampleDatabase

/-- On an instance whose positions are not linearly ordered, the count is `0`. -/
axiom weightedWorlds_of_not_isLinOrd :
  ∀ {L : Language.{0, 0}} [Finite (Σ n, L.Relations n)] [L.IsRelational] (φ : L.Sentence)
      (A : Type) [(weightedLang L).Structure A],
    ¬IsLinOrd (WLe L A) → WeightedWorlds φ A = 0

end Lax794877.ProbabilityRatio
end
