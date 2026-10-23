-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
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
import Mathlib.Order.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

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

/-- A relativized ordered first-order reduction from `P` to `Q`. -/
structure RelOrderedFOReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L) (Q : DecisionProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : RelFOInterpretation (L.sum Language.order) L' Tag dim
  /-- The definable domain is inhabited: some tagged tuple satisfies its tag's
  domain formula. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (w : Fin dim → A), (toRelInterpretation.domFormula t).Realize w
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toRelInterpretation.MapRel A)

end Lax904597.Relativized
end

-- Lax366625.CountingProblems
section
namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.CountingProblem.ofFun
end Lax366625.CountingProblems.CountingProblem.ofFun

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

/-- The decision problem underneath a counting problem: is the count
positive? -/
def support (C : CountingProblem L) : DecisionProblem L where
  Holds := fun A inst => 0 < @Count L _ C A inst
  iso_invariant := fun e => by rw [C.iso_invariant e]

end CountingProblem

variable {L} {L' : Language.{0, 0}}

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-- An ordered parsimonious reduction through a **relativized**
interpretation: the two counts agree, the target structure being carried by
the definable subset of `Tag × A^dim` that the domain formula carves out. -/
structure RelOrderedParsimoniousReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : RelFOInterpretation (L.sum Language.order) L' Tag dim
  /-- The definable domain is inhabited. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (w : Fin dim → A), (toRelInterpretation.domFormula t).Realize w
  /-- The counts agree, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = D (toRelInterpretation.MapRel A)

end Lax366625.CountingProblems
end

-- Lax366625.CountingClasses
section
namespace Lax366625.CountingClasses

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax366625.CountingProblems

/-- A counting class: a membership predicate and a hardness predicate on
counting problems, over arbitrary relational vocabularies. -/
structure CountingClass where
  /-- The counting problems belonging to the class. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], CountingProblem L → Prop
  /-- The counting problems every problem of the class reduces to. -/
  ParsimoniousHard : ∀ {L : Language.{0, 0}} [L.IsRelational], CountingProblem L → Prop

/-- The class with the given membership, a problem being hard when every member
reduces to it by a relativized ordered parsimonious reduction. -/
def CountingClass.ofMem
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], CountingProblem L₀ → Prop) :
    CountingClass where
  Mem C := Mem C
  ParsimoniousHard C := ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
    Mem D → Nonempty (RelOrderedParsimoniousReduction D C)

end Lax366625.CountingClasses
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

-- Lax535992.DeterministicMachines
section
namespace Lax535992
end Lax535992

namespace Lax535992.DeterministicMachines
end Lax535992.DeterministicMachines

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData
end

-- Lax366625.MachineNumbers
section
namespace Lax366625.MachineNumbers

open Lax904597.Machines

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

end Ripple

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive tapeOutRel : ℕ → Type where
/-- `out p`: the cell `p` is an output cell, holding one digit. -/
  | out : tapeOutRel 1
/-- `one a`: the symbol `a` is read as the digit `1`. -/
  | one : tapeOutRel 1
  deriving DecidableEq

/-- The symbols reading a number off the tape of a machine. -/
def tapeOut : FirstOrder.Language :=
  ⟨fun _ => Empty, tapeOutRel⟩

instance instIsRelationalTapeOut : FirstOrder.Language.IsRelational tapeOut := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- The relational language of machines writing a number. -/
abbrev turingOut : Language.{0, 0} := turing.sum tapeOut

open FirstOrder

open Language Structure

namespace TMData

variable {A : Type} (M : TMData A)

end TMData

/-- A machine writing a number is a machine. -/
instance turingOutStructure (A : Type) [turingOut.Structure A] :
    turing.Structure A :=
  (LHom.sumInl : turing →ᴸ turingOut).reduct A

section Semantics

variable {A : Type} [turingOut.Structure A]

end Semantics

open Lax366625.CountingProblems

end Lax366625.MachineNumbers
end

-- Lax904597.SecondOrder
section
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

/-- The structure over the block's vocabulary determined by an assignment. -/
@[reducible]
def SOBlock.structure (B : SOBlock) {A : Type} (ρ : B.Assignment A) :
    B.lang.Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {_} r x => ρ r.1 fun j => x (Fin.cast r.2 j)

/-- The base vocabulary expanded by the vocabularies of a list of blocks. -/
def soLang (L : Language.{0, 0}) : List SOBlock → Language.{0, 0}
  | [] => L
  | B :: Bs => soLang (L.sum B.lang) Bs

/-- Alternating second-order satisfaction: the sentence obtained from the
first-order kernel `φ` by quantifying the blocks `Bs` alternately,
existentially first when `pol` is `true`, holds in the `L`-structure `A`. -/
def SORealize (L : Language.{0, 0}) (A : Type) [inst : L.Structure A] :
    ∀ (Bs : List SOBlock), (soLang L Bs).Sentence → Bool → Prop
  | [], φ, _ => @Sentence.Realize L A inst φ
  | B :: Bs, φ, true =>
      ∃ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
          Bs φ false
  | B :: Bs, φ, false =>
      ∀ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
          Bs φ true

variable {L : Language.{0, 0}}

/-- A decision problem is `Σₖ`-definable if, on nonempty finite structures, it
is defined by a second-order sentence with `k` alternating blocks of
second-order quantifiers, starting existentially. -/
def SigmaSODefinable [L.IsRelational] (k : ℕ) (P : DecisionProblem L) : Prop :=
  ∃ Bs : List SOBlock, Bs.length = k ∧
    ∃ φ : (soLang L Bs).Sentence,
      ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ SORealize L A Bs φ true

end Lax904597.SecondOrder
end

-- Lax366625.CountingRuns
section
namespace Lax366625.CountingRuns
end Lax366625.CountingRuns

namespace Lax366625.CountingRuns.TMData
end Lax366625.CountingRuns.TMData
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

-- Lax366625.CountingSat
section
namespace Lax366625.CountingSat
end Lax366625.CountingSat
end

-- Lax535992.HornSat
section
namespace Lax535992
end Lax535992

namespace Lax535992.HornSat
end Lax535992.HornSat
end

-- Lax366625.HornNumbers
section
namespace Lax366625.HornNumbers.ForcedIn
end Lax366625.HornNumbers.ForcedIn

namespace Lax366625.HornNumbers

open Lax535992.HornSat Lax904597.Sat

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section LeastModel

variable {A : Type} [sat.Structure A]

end LeastModel

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive digitOrderRel : ℕ → Type where
/-- `out x`: the element `x` holds one digit. -/
  | out : digitOrderRel 1
/-- `below y x`: the digit of `y` is at most as significant as the one of
  `x`. -/
  | below : digitOrderRel 2
  deriving DecidableEq

/-- The symbols reading a number off a set of marked elements. -/
def digitOrder : FirstOrder.Language :=
  ⟨fun _ => Empty, digitOrderRel⟩

instance instIsRelationalDigitOrder : FirstOrder.Language.IsRelational digitOrder := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- The relational language of Horn formulas writing a number. -/
abbrev satOut : Language.{0, 0} := sat.sum digitOrder

open FirstOrder

open Language Structure

/-- A Horn formula writing a number is a CNF instance. -/
instance satOutStructure (A : Type) [satOut.Structure A] :
    sat.Structure A :=
  (LHom.sumInl : sat →ᴸ satOut).reduct A

section Semantics

variable {A : Type} [satOut.Structure A]

end Semantics

open Lax366625.CountingProblems

end Lax366625.HornNumbers
end

-- Lax535992.CircuitValue
section
namespace Lax535992.CircuitValue.GateVal
end Lax535992.CircuitValue.GateVal

namespace Lax535992.CircuitValue

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive circuitRel : ℕ → Type where
/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
  | isTrue : circuitRel 1
/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
  | isFalse : circuitRel 1
/-- `isAnd g`: the element `g` is a conjunction gate. -/
  | isAnd : circuitRel 1
/-- `isOr g`: the element `g` is a disjunction gate. -/
  | isOr : circuitRel 1
/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
  | isNot : circuitRel 1
/-- `out g`: the element `g` is an output gate. -/
  | out : circuitRel 1
/-- `left g x`: the gate `g` takes `x` as its first argument. -/
  | left : circuitRel 2
/-- `right g x`: the gate `g` takes `x` as its second argument. -/
  | right : circuitRel 2
  deriving DecidableEq

/-- The relational language of Boolean circuits: one unary predicate per gate
kind, one marking the output, and two binary predicates wiring a gate to its
arguments. -/
def circuit : FirstOrder.Language :=
  ⟨fun _ => Empty, circuitRel⟩

instance instIsRelationalCircuit : FirstOrder.Language.IsRelational circuit := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Semantics

variable {A : Type} [circuit.Structure A]

end Semantics

end Lax535992.CircuitValue
end

-- Lax366625.NumberedCircuits
section
namespace Lax366625.NumberedCircuits

open Lax535992.CircuitValue

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive numCircuitRel : ℕ → Type where
/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
  | isTrue : numCircuitRel 1
/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
  | isFalse : numCircuitRel 1
/-- `isAnd g`: the element `g` is a conjunction gate. -/
  | isAnd : numCircuitRel 1
/-- `isOr g`: the element `g` is a disjunction gate. -/
  | isOr : numCircuitRel 1
/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
  | isNot : numCircuitRel 1
/-- `out g`: the element `g` is an output gate, holding one digit. -/
  | out : numCircuitRel 1
/-- `left g x`: the gate `g` takes `x` as its first argument. -/
  | left : numCircuitRel 2
/-- `right g x`: the gate `g` takes `x` as its second argument. -/
  | right : numCircuitRel 2
/-- `below h g`: the digit held by `h` is at most as significant as the one
  held by `g`. -/
  | below : numCircuitRel 2
  deriving DecidableEq

/-- The relational language of Boolean circuits writing a number: the symbols
of circuits, and a comparison of the output gates. -/
def numCircuit : FirstOrder.Language :=
  ⟨fun _ => Empty, numCircuitRel⟩

instance instIsRelationalNumCircuit : FirstOrder.Language.IsRelational numCircuit := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `isTrue g`: the element `g` is a constant input gate holding `1`. -/
abbrev ncIsTrue : numCircuit.Relations 1 :=
  .isTrue

/-- `isFalse g`: the element `g` is a constant input gate holding `0`. -/
abbrev ncIsFalse : numCircuit.Relations 1 :=
  .isFalse

/-- `isAnd g`: the element `g` is a conjunction gate. -/
abbrev ncIsAnd : numCircuit.Relations 1 :=
  .isAnd

/-- `isOr g`: the element `g` is a disjunction gate. -/
abbrev ncIsOr : numCircuit.Relations 1 :=
  .isOr

/-- `isNot g`: the element `g` is a negation gate, its argument read off
  `left`. -/
abbrev ncIsNot : numCircuit.Relations 1 :=
  .isNot

/-- `out g`: the element `g` is an output gate, holding one digit. -/
abbrev ncOut : numCircuit.Relations 1 :=
  .out

/-- `left g x`: the gate `g` takes `x` as its first argument. -/
abbrev ncLeft : numCircuit.Relations 2 :=
  .left

/-- `right g x`: the gate `g` takes `x` as its second argument. -/
abbrev ncRight : numCircuit.Relations 2 :=
  .right

open FirstOrder

open Language Structure

/-- Forgetting the comparison of the outputs: the vocabulary of circuits, read
in the vocabulary of circuits writing a number. -/
def circuitOfNum : circuit →ᴸ numCircuit where
  onFunction := fun {_} f => isEmptyElim f
  onRelation := fun {n} R =>
    match n, R with
    | _, .isTrue => ncIsTrue
    | _, .isFalse => ncIsFalse
    | _, .isAnd => ncIsAnd
    | _, .isOr => ncIsOr
    | _, .isNot => ncIsNot
    | _, .out => ncOut
    | _, .left => ncLeft
    | _, .right => ncRight

/-- A circuit writing a number is a circuit. -/
instance numCircuitStructure (A : Type) [numCircuit.Structure A] :
    circuit.Structure A :=
  circuitOfNum.reduct A

section Semantics

variable {A : Type} [numCircuit.Structure A]

end Semantics

open Lax366625.CountingProblems

end Lax366625.NumberedCircuits
end

-- Lax485149.SecondOrderAtoms
section
namespace Lax485149.SecondOrderAtoms

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- An atom `R i (x_{f 0}, …)` in the relation variables of a block, with
arguments read from `k` universally quantified first-order variables. -/
structure SOAtom (B : SOBlock) (k : ℕ) where
  /-- The relation variable of the block the atom is about. -/
  idx : B.ι
  /-- The arguments, as indices among the `k` universally quantified
  variables. -/
  args : Fin (B.arity idx) → Fin k

variable {B : SOBlock} {k : ℕ}

/-- The truth value of a second-order atom under an assignment of the block
and a valuation of the universally quantified variables. -/
def SOAtom.Holds {A : Type} (a : SOAtom B k) (ρ : B.Assignment A) (v : Fin k → A) : Prop :=
  ρ a.idx fun j => v (a.args j)

end Lax485149.SecondOrderAtoms
end

-- Lax535992.HornFragment
section
namespace Lax535992.HornFragment

open Lax485149.SecondOrderAtoms Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A Horn clause over the input vocabulary `L` and the block `B`, with `k`
universally quantified first-order variables: an arbitrary first-order guard
over `L` and a list of second-order body atoms imply the head atom – or `⊥`,
when the head is `none` (a *goal* clause). -/
structure HornClause (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) where
  /-- The first-order guard, over the input vocabulary alone. -/
  guard : L.Formula (Fin k)
  /-- The body: second-order atoms, all of them positive. -/
  body : List (SOAtom B k)
  /-- The head: a second-order atom, or `none` for a goal clause. -/
  head : Option (SOAtom B k)

/-- An SO-Horn kernel, as data: a finite conjunction of Horn clauses, each
implicitly universally quantified over the same `k` first-order variables. -/
abbrev HornProgram (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) : Type :=
  List (HornClause L B k)

section Semantics

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {A : Type} [L.Structure A]

/-- The truth value of the head of a clause: `False` for a goal clause. -/
def HornClause.HeadHolds (c : HornClause L B k) (ρ : B.Assignment A)
    (v : Fin k → A) : Prop :=
  c.head.elim False fun h => h.Holds ρ v

/-- A Horn clause holds at a valuation when its guard and all its body atoms
force its head. -/
def HornClause.Holds (c : HornClause L B k) (ρ : B.Assignment A) (v : Fin k → A) :
    Prop :=
  (c.guard.Realize v ∧ ∀ a ∈ c.body, a.Holds ρ v) → c.HeadHolds ρ v

/-- An assignment satisfies a program when every clause holds at every
valuation of the universally quantified variables. -/
def HornProgram.Holds (prog : HornProgram L B k) (ρ : B.Assignment A) : Prop :=
  ∀ v : Fin k → A, ∀ c ∈ prog, c.Holds ρ v

end Semantics

/-- A decision problem is *SO-Horn definable* if, on nonempty finite *ordered*
structures, it is defined by an existential second-order sentence with a Horn
kernel: there is a block of relation variables and a Horn program over the
ordered expansion of the vocabulary such that the yes-instances are exactly
the structures admitting a satisfying assignment. A single block suffices,
since existential second-order quantifiers merge.

The guards live over `L.sum Language.order`, and the equivalence is required
for *every* linear order on `A`: since the problem itself does not see the
order, this is order-invariant SO-Horn definability. -/
def SigmaSOHornDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ (B : SOBlock) (k : ℕ) (prog : HornProgram (L.sum Language.order) B k),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ ∃ ρ : B.Assignment A, prog.Holds ρ

end Lax535992.HornFragment
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

-- Lax366625.SecondOrderCounting
section
namespace Lax366625.SecondOrderCounting
end Lax366625.SecondOrderCounting

namespace Lax366625.SecondOrderCounting.SQTerm
end Lax366625.SecondOrderCounting.SQTerm

namespace Lax366625.SecondOrderCounting.SQTerm.add
end Lax366625.SecondOrderCounting.SQTerm.add

namespace Lax366625.SecondOrderCounting.SQTerm.const
end Lax366625.SecondOrderCounting.SQTerm.const

namespace Lax366625.SecondOrderCounting.SQTerm.eval
end Lax366625.SecondOrderCounting.SQTerm.eval

namespace Lax366625.SecondOrderCounting.SQTerm.ind
end Lax366625.SecondOrderCounting.SQTerm.ind

namespace Lax366625.SecondOrderCounting.SQTerm.mul
end Lax366625.SecondOrderCounting.SQTerm.mul

namespace Lax366625.SecondOrderCounting.SQTerm.prod
end Lax366625.SecondOrderCounting.SQTerm.prod

namespace Lax366625.SecondOrderCounting.SQTerm.sosum
end Lax366625.SecondOrderCounting.SQTerm.sosum

namespace Lax366625.SecondOrderCounting.SQTerm.sum
end Lax366625.SecondOrderCounting.SQTerm.sum
end

-- Lax366625.WitnessCounting
section
namespace Lax366625.WitnessCounting

open Lax366625.CountingProblems Lax904597.SecondOrder

open FirstOrder

open Language Structure

section Witness

variable {L : Language.{0, 0}}

/-- The number of assignments of the block `B` on the structure `A` under which
the first-order kernel `φ` holds. -/
noncomputable def witnessCount (B : SOBlock) (φ : (L.sum B.lang).Sentence) (A : Type)
    [inst : L.Structure A] : ℕ :=
  Nat.card {ρ : B.Assignment A //
    @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ)) φ}

end Witness

section Definable

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A counting problem is **`#P`-definable** if, on nonempty finite structures,
it counts the witnesses of an existential second-order sentence over the
ordered expansion: for some block `B` and first-order kernel `φ`, its value is
the number of assignments of `B` satisfying `φ`, whatever the linear order of
the instance. -/
def SharpPDefinable (C : CountingProblem L) : Prop :=
  ∃ (B : SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      C A = witnessCount B φ A

end Definable

open Lax366625.CountingClasses

/-- **#P**: the class of the `#P`-definable counting problems. -/
def SharpP : CountingClass :=
  CountingClass.ofMem fun C => SharpPDefinable C

end Lax366625.WitnessCounting
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

-- Lax904597.Classes
section
namespace Lax904597.Classes

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

/-- A complexity class: a membership predicate and a hardness predicate on
decision problems, over arbitrary relational vocabularies. -/
structure ComplexityClass where
  /-- The problems belonging to the class. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop
  /-- The problems every problem of the class reduces to. -/
  Hard : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop

variable {L : Language.{0, 0}} [L.IsRelational]

/-- Cofinal hardness for a collection of problems: every problem of the
collection reduces to every relational problem that `P` reduces to. -/
def CofinalHard (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) : Prop :=
  ∀ {L' : Language.{0, 0}} [L'.IsRelational] (S : DecisionProblem L'),
    Nonempty (RelOrderedFOReduction P S) →
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        Mem Q → Nonempty (RelOrderedFOReduction Q S)

/-- The class with the given membership and cofinal hardness. -/
def ComplexityClass.ofMem
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop) :
    ComplexityClass where
  Mem P := Mem P
  Hard P := CofinalHard Mem P

/-- The level `Σₖ₊₁ᵖ` of the polynomial hierarchy: the problems definable with
`k + 1` alternating blocks of second-order quantifiers, existential first. -/
def sigmaLevel (k : ℕ) : ComplexityClass :=
  .ofMem fun P => SigmaSODefinable (k + 1) P

/-- NP is `Σ₁ᵖ`: by definition, the existential-second-order definable
problems (Fagin's theorem). -/
def NP : ComplexityClass := sigmaLevel 0

end Lax904597.Classes
end

-- Lax535992.ClassPTIME
section
namespace Lax535992.ClassPTIME

open Lax904597.Problems Lax904597.Classes Lax485149.Complement Lax535992.HornFragment

/-- **PTIME**: the class of the SO-Horn definable problems, with cofinal
hardness. -/
def PTIME : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSOHornDefinable P

end Lax535992.ClassPTIME
end

-- Lax366625.SharpPAndNP
section
namespace Lax366625.SharpPAndNP

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Sat Lax904597.Machines

open Lax535992.ClassPTIME

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting

open Lax366625.SecondOrderCounting

open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers

open Lax366625.CountingRuns

open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- A parsimoniously #P-hard problem with support in PTIME gives NP ⊆ PTIME. -/
axiom NP_subset_PTIME_of_sharpP_parsimoniousHard :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
  SharpP.ParsimoniousHard C → PTIME.Mem C.support →
    ∀ {L' : Language.{0, 0}} [L'.IsRelational] (P : DecisionProblem L'), NP.Mem P → PTIME.Mem P

end Lax366625.SharpPAndNP
end
