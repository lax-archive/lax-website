-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.SetTheory.Cardinal.Finite

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

/-- The structure over the block's vocabulary determined by an assignment. -/
@[reducible]
def SOBlock.structure (B : SOBlock) {A : Type} (ρ : B.Assignment A) :
    B.lang.Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {_} r x => ρ r.1 fun j => x (Fin.cast r.2 j)

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax535992.InflationaryFixedPoint
section
namespace Lax535992.InflationaryFixedPoint

open Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- The structure over `L` expanded by one copy of a block's vocabulary,
interpreted by an assignment. -/
@[reducible]
def SOBlock.structure₁ {L : Language.{0, 0}} (B : SOBlock) {A : Type} [inst : L.Structure A]
    (ρ : B.Assignment A) : (L.sum B.lang).Structure A :=
  @sumStructure L B.lang A inst (B.structure ρ)

/-- A simultaneous first-order induction: a block of relation variables, one
first-order step formula per variable – over the base vocabulary expanded by
the block, its free variables the arguments of the variable – and an output
sentence over the same expanded vocabulary, read at the value of the
iteration. The step formulas are *unrestricted*. -/
structure StepDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the iteration. -/
  B : SOBlock
  /-- The step formula of each variable; its free variables are the arguments
  of the variable. -/
  step : ∀ i : B.ι, (L.sum B.lang).Formula (Fin (B.arity i))
  /-- The first-order output, over the expanded vocabulary – unrestricted, in
  particular free to negate fixed-point atoms. -/
  out : (L.sum B.lang).Sentence

namespace StepDef

variable {L : Language.{0, 0}} (d : StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

end Semantics

end StepDef

end Lax535992.InflationaryFixedPoint
end

-- Lax134656.SecondOrderTransitiveClosure
section
namespace Lax134656.SecondOrderTransitiveClosure

open Lax904597.Problems Lax904597.SecondOrder Lax535992.InflationaryFixedPoint

open FirstOrder

open Language Structure

/-- The structure over `L` expanded by *two* copies of a block's vocabulary –
the current state and the next one – interpreted by two assignments. -/
@[reducible]
def SOBlock.structure₂ {L : Language.{0, 0}} (B : SOBlock) {A : Type} [inst : L.Structure A]
    (ρ σ : B.Assignment A) : ((L.sum B.lang).sum B.lang).Structure A :=
  @sumStructure (L.sum B.lang) B.lang A (SOBlock.structure₁ B ρ) (B.structure σ)

/-- A single-`TC` definition over a second-order block: the states of the walk
are the assignments of the block `B`, and the transition, source, and target
conditions are first-order sentences over the base vocabulary expanded by the
order and by copies of the block. The transition sentence sees two copies –
the current state and the next one.

The order is visible to all three sentences; the problem itself does not see
it. -/
structure SOTCSpec (L : Language.{0, 0}) : Type 1 where
  /-- The block whose assignments are the states of the walk. -/
  B : SOBlock
  /-- The transition sentence, over two copies of the block: the current state
  reads the first copy, the next state the second. -/
  step : (((L.sum Language.order).sum B.lang).sum B.lang).Sentence
  /-- The sentence defining the admissible starting states. -/
  src : ((L.sum Language.order).sum B.lang).Sentence
  /-- The sentence defining the accepting states. -/
  tgt : ((L.sum Language.order).sum B.lang).Sentence

namespace SOTCSpec

section Semantics

variable {L : Language.{0, 0}} (spec : SOTCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

variable (A) in
/-- A state of the walk: an assignment of the block. -/
abbrev State : Type := spec.B.Assignment A

/-- One step of the walk: the transition sentence, read with the current state
in the first copy of the block and the next state in the second. -/
def Step (ρ σ : spec.State A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₂ (L := L.sum Language.order) spec.B ρ σ) spec.step

/-- Reachability in the walk: the reflexive-transitive closure of
`SOTCSpec.Step`. -/
abbrev Reach : spec.State A → spec.State A → Prop :=
  Relation.ReflTransGen spec.Step

/-- A state is a starting state when it satisfies the source sentence. -/
def IsSrc (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ (L := L.sum Language.order) spec.B ρ) spec.src

/-- A state is accepting when it satisfies the target sentence. -/
def IsTgt (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ (L := L.sum Language.order) spec.B ρ) spec.tgt

variable (A) in
/-- The structure is accepted: some accepting state is reachable from some
starting state. -/
def Accepts : Prop :=
  ∃ ρ σ : spec.State A, spec.IsSrc ρ ∧ spec.IsTgt σ ∧ spec.Reach ρ σ

end Semantics

end SOTCSpec

/-- A decision problem is *SO(TC) definable* if, on nonempty finite *ordered*
structures, it is defined by a single transitive closure over the assignments
of a second-order quantifier block: there is an `SOTCSpec` whose accepting
states are reachable from its starting states exactly on the yes-instances.
The equivalence is required for *every* linear order on the universe: the
problem itself does not see the order, while the three sentences may. -/
def SOTCDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : SOTCSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.Accepts A

end Lax134656.SecondOrderTransitiveClosure
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

/-- A problem is complete for a class if it belongs to it and is hard for
it. -/
def ComplexityClass.Complete (C : ComplexityClass) (P : DecisionProblem L) : Prop :=
  C.Mem P ∧ C.Hard P

end Lax904597.Classes
end

-- Lax134656.ClassPSPACE
section
namespace Lax134656.ClassPSPACE

open Lax904597.Problems Lax904597.Classes Lax485149.Complement

open Lax134656.SecondOrderTransitiveClosure

/-- **PSPACE**: the class of the SO(TC) definable problems, with cofinal
hardness. -/
def PSPACE : ComplexityClass :=
  ComplexityClass.ofMem fun P => SOTCDefinable P

end Lax134656.ClassPSPACE
end

-- Lax134656.OrderFreeTransitiveClosure
section
namespace Lax134656.OrderFreeTransitiveClosure
end Lax134656.OrderFreeTransitiveClosure

namespace Lax134656.OrderFreeTransitiveClosure.SOTCSpecFree
end Lax134656.OrderFreeTransitiveClosure.SOTCSpecFree
end

-- Lax134656.PartialFixedPoint
section
namespace Lax134656
end Lax134656

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef
end

-- Lax485149.Problems
section
namespace Lax485149.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax485149.Problems
end

-- Lax134656.Qsat
section
namespace Lax134656.Qsat.QsatWf
end Lax134656.Qsat.QsatWf

namespace Lax134656.Qsat.QsatWins
end Lax134656.Qsat.QsatWins

namespace Lax134656.Qsat

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive qsatRel : ℕ → Type where
/-- `isVar x`: the element `x` is a quantified propositional variable. -/
  | isVar : qsatRel 1
/-- `allVar x`: the variable `x` is quantified universally. -/
  | allVar : qsatRel 1
/-- `prefixLt x y`: the variable `x` is quantified outside the variable
  `y`. -/
  | prefixLt : qsatRel 2
/-- `isClause c`: the element `c` is a clause of the matrix. -/
  | isClause : qsatRel 1
/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : qsatRel 2
/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : qsatRel 2
  deriving DecidableEq

/-- The relational vocabulary of fully quantified Boolean formulas: that of
CNF instances, together with the marks and the order describing the quantifier
prefix. -/
def qsat : FirstOrder.Language :=
  ⟨fun _ => Empty, qsatRel⟩

instance instIsRelationalQsat : FirstOrder.Language.IsRelational qsat := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Reading

variable {A : Type} [qsat.Structure A]

end Reading

section Game

variable {A : Type} [qsat.Structure A]

end Game

section Problem

variable {A : Type} [qsat.Structure A]

end Problem

end Lax134656.Qsat
end

-- Lax904597.Machines
section
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

/-- `p` is a lowest position. -/
def MinPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le p q

/-- `q` is the next position above `p`. -/
def SuccPos (Le : A → A → Prop) (Posn : A → Prop) (p q : A) : Prop :=
  Posn p ∧ Posn q ∧ Le p q ∧ p ≠ q ∧ ∀ r, Posn r → Le p r → Le r q → r = p ∨ r = q

/-- A configuration: the current state, the position of the head, and the
contents of the tape. -/
@[ext]
structure Config (A : Type) where
  /-- The current state. -/
  state : A
  /-- The cell the head is on. -/
  head : A
  /-- The symbol in each cell. -/
  tape : A → A

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

/-- The symbols a cell may initially hold: the input symbol where the input is
defined, the blank elsewhere. -/
def InitTape (p a : A) : Prop := M.Inp p a ∨ ((∀ b, ¬ M.Inp p b) ∧ M.Blank a)

/-- Being an initial configuration: a start state, the head on the lowest
position, and an initial tape. -/
def IsInit (c : Config A) : Prop :=
  M.Start c.state ∧ MinPos M.Le M.Posn c.head ∧ ∀ p, M.InitTape p (c.tape p)

/-- One step: some transition applies in the current state to the symbol under
the head; it writes in that cell, changes state, and moves the head to the
neighboring position in the direction it names. Other cells are unchanged,
and a move off the end of the tape is impossible, so the run stops there. -/
def Step (c c' : Config A) : Prop :=
  ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧
    M.Dst τ c'.state ∧ M.Write τ (c'.tape c.head) ∧
    (∀ p, p ≠ c.head → c'.tape p = c.tape p) ∧
    ((M.Right τ ∧ SuccPos M.Le M.Posn c.head c'.head) ∨
      (¬ M.Right τ ∧ SuccPos M.Le M.Posn c'.head c.head))

/-- Well-formedness: the order is linear, there is a position to start on, the
input is functional, and there is exactly one blank symbol. -/
def WellFormed : Prop :=
  IsLinOrd M.Le ∧ (∃ p, M.Posn p) ∧
    (∀ p a b, M.Inp p a → M.Inp p b → a = b) ∧
    (∃ b, M.Blank b) ∧ (∀ a b, M.Blank a → M.Blank b → a = b)

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

/-- The position symbol. -/
abbrev tmPosn : turing.Relations 1 := .posn

/-- The transition symbol. -/
abbrev tmTr : turing.Relations 1 := .tr

/-- The start-state symbol. -/
abbrev tmStart : turing.Relations 1 := .start

/-- The accepting-state symbol. -/
abbrev tmAcc : turing.Relations 1 := .acc

/-- The blank symbol. -/
abbrev tmBlank : turing.Relations 1 := .blank

/-- The move-right symbol. -/
abbrev tmRight : turing.Relations 1 := .right

/-- The order symbol. -/
abbrev tmLe : turing.Relations 2 := .le

/-- The transition-source symbol. -/
abbrev tmSrc : turing.Relations 2 := .tsrc

/-- The transition-read symbol. -/
abbrev tmRead : turing.Relations 2 := .tread

/-- The transition-destination symbol. -/
abbrev tmDst : turing.Relations 2 := .tdst

/-- The transition-write symbol. -/
abbrev tmWrite : turing.Relations 2 := .twrite

/-- The input symbol. -/
abbrev tmInp : turing.Relations 2 := .inp

section Shorthands

variable [turing.Structure A]

/-- Being a position. -/
def TMPosn (a : A) : Prop := RelMap tmPosn ![a]

/-- Being a transition. -/
def TMTr (a : A) : Prop := RelMap tmTr ![a]

/-- Being a start state. -/
def TMStart (a : A) : Prop := RelMap tmStart ![a]

/-- Being an accepting state. -/
def TMAcc (a : A) : Prop := RelMap tmAcc ![a]

/-- Being the blank symbol. -/
def TMBlank (a : A) : Prop := RelMap tmBlank ![a]

/-- Moving the head right. -/
def TMRight (a : A) : Prop := RelMap tmRight ![a]

/-- The order on positions. -/
def TMLe (a b : A) : Prop := RelMap tmLe ![a, b]

/-- The state a transition applies in. -/
def TMSrc (a b : A) : Prop := RelMap tmSrc ![a, b]

/-- The symbol a transition reads. -/
def TMRead (a b : A) : Prop := RelMap tmRead ![a, b]

/-- The state a transition moves to. -/
def TMDst (a b : A) : Prop := RelMap tmDst ![a, b]

/-- The symbol a transition writes. -/
def TMWrite (a b : A) : Prop := RelMap tmWrite ![a, b]

/-- The initial contents of a cell. -/
def TMInp (a b : A) : Prop := RelMap tmInp ![a, b]

end Shorthands

/-- The machine an instance describes. -/
def tmData (A : Type) [turing.Structure A] : TMData A where
  Posn := TMPosn
  Le := TMLe
  Tr := TMTr
  Start := TMStart
  Acc := TMAcc
  Blank := TMBlank
  Right := TMRight
  Src := TMSrc
  Read := TMRead
  Dst := TMDst
  Write := TMWrite
  Inp := TMInp

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

-- Lax134656.SpaceBoundedMachines
section
namespace Lax134656.SpaceBoundedMachines

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Machines Lax485149.Problems Lax535992.DeterministicMachines

namespace TMData

variable {A : Type} (M : TMData A)

/-- **Acceptance in bounded space**: some run from an initial configuration
reaches an accepting state, with *no bound on its length*. The space is
bounded by construction, the tape being indexed by the positions; a run may
visit exponentially many configurations, so acceptance is reachability in the
configuration graph. -/
def AcceptsSpace : Prop :=
  ∃ c₀ c : Config A, M.IsInit c₀ ∧ Relation.ReflTransGen M.Step c₀ c ∧ M.Acc c.state

end TMData

/-- The instance is a well-formed machine accepting in bounded space. -/
def NTMAcceptsSpace (A : Type) [turing.Structure A] : Prop :=
  (tmData A).WellFormed ∧ TMData.AcceptsSpace (tmData A)

/-- Machine acceptance in bounded space. -/
def NTMAcceptSpace : DecisionProblem turing :=
  DecisionProblem.ofPred fun A _ => NTMAcceptsSpace A

end Lax134656.SpaceBoundedMachines
end

-- Lax134656.SuccinctReach
section
namespace Lax134656.SuccinctReach

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive transSysRel : ℕ → Type where
/-- `stateVar x`: the element `x` is a state variable. -/
  | stateVar : transSysRel 1
/-- `next x y`: the element `y` is the next-state copy of the state
  variable `x`. -/
  | next : transSysRel 2
/-- `stepCl c`: the element `c` is a clause of the transition formula. -/
  | stepCl : transSysRel 1
/-- `srcCl c`: the element `c` is a clause of the source formula. -/
  | srcCl : transSysRel 1
/-- `tgtCl c`: the element `c` is a clause of the target formula. -/
  | tgtCl : transSysRel 1
/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : transSysRel 2
/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : transSysRel 2
  deriving DecidableEq

/-- The relational vocabulary of succinctly described transition systems: the
state variables and their next-state copies, three groups of clauses, and the
two literal-occurrence predicates of CNF instances. -/
def transSys : FirstOrder.Language :=
  ⟨fun _ => Empty, transSysRel⟩

instance instIsRelationalTransSys : FirstOrder.Language.IsRelational transSys := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Semantics

variable (A : Type) [transSys.Structure A]

end Semantics

end Lax134656.SuccinctReach
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

-- Lax535992.ClassPTIME
section
namespace Lax535992.ClassPTIME
end Lax535992.ClassPTIME
end

-- Lax564036.Hierarchy
section
namespace Lax564036
end Lax564036

namespace Lax564036.Hierarchy
end Lax564036.Hierarchy

namespace Lax564036.Hierarchy.SigmaP
end Lax564036.Hierarchy.SigmaP
end

-- Lax134656.SpaceMachinesPSPACEComplete
section
namespace Lax134656.SpaceMachinesPSPACEComplete

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Machines

open Lax485149.Problems Lax485149.Complement

open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME

open Lax564036.Hierarchy

open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure

open Lax134656.PartialFixedPoint

open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- The problem is PSPACE-complete. -/
axiom ntmAcceptSpace_PSPACE_complete : PSPACE.Complete NTMAcceptSpace

end Lax134656.SpaceMachinesPSPACEComplete
end
