-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Order.Basic

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

end Lax904597.Classes
end

-- Lax485149.ClassL
section
namespace Lax485149.ClassL
end Lax485149.ClassL
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

-- Lax485149.KromFragment
section
namespace Lax485149.KromFragment

open Lax485149.SecondOrderAtoms Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A literal in the relation variables of a block: an atom together with a
sign (`positive = false` for a negated atom). -/
structure KromLit (B : SOBlock) (k : ℕ) where
  /-- The underlying second-order atom. -/
  atom : SOAtom B k
  /-- The sign of the literal: `true` for the atom, `false` for its
  negation. -/
  positive : Bool

/-- A Krom clause over the input vocabulary `L` and the block `B`, with `k`
universally quantified first-order variables: an arbitrary first-order guard
over `L` implies the disjunction of at most two signed second-order literals.
A `none` literal is absent, so a clause with both literals absent is the goal
clause `guard → ⊥`. -/
structure KromClause (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) where
  /-- The first-order guard, over the input vocabulary alone. -/
  guard : L.Formula (Fin k)
  /-- The first literal of the clause, if any. -/
  lit₁ : Option (KromLit B k)
  /-- The second literal of the clause, if any. -/
  lit₂ : Option (KromLit B k)

/-- An SO-Krom kernel, as data: a finite conjunction of Krom clauses, each
implicitly universally quantified over the same `k` first-order variables. -/
abbrev KromProgram (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) : Type :=
  List (KromClause L B k)

section Semantics

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {A : Type} [L.Structure A]

/-- The truth value of a literal: its atom, or the negation of its atom. -/
def KromLit.Holds (l : KromLit B k) (ρ : B.Assignment A) (v : Fin k → A) : Prop :=
  if l.positive then l.atom.Holds ρ v else ¬l.atom.Holds ρ v

/-- The truth value of one of the two literal slots of a clause: `False` when
the literal is absent. -/
def KromLit.slotHolds (o : Option (KromLit B k)) (ρ : B.Assignment A) (v : Fin k → A) :
    Prop :=
  o.elim False fun l => l.Holds ρ v

/-- A Krom clause holds at a valuation when its guard forces one of its (at
most two) literals. -/
def KromClause.Holds (c : KromClause L B k) (ρ : B.Assignment A) (v : Fin k → A) :
    Prop :=
  c.guard.Realize v →
    (KromLit.slotHolds c.lit₁ ρ v ∨ KromLit.slotHolds c.lit₂ ρ v)

/-- An assignment satisfies a program when every clause holds at every
valuation of the universally quantified variables. -/
def KromProgram.Holds (prog : KromProgram L B k) (ρ : B.Assignment A) : Prop :=
  ∀ v : Fin k → A, ∀ c ∈ prog, c.Holds ρ v

end Semantics

variable {L : Language.{0, 0}}

/-- A decision problem is *SO-Krom definable* if, on nonempty finite *ordered*
structures, it is defined by an existential second-order sentence with a Krom
kernel: there is a block of relation variables and a Krom program over the
ordered expansion of the vocabulary such that the yes-instances are exactly
the structures admitting a satisfying assignment. A single block suffices,
since existential second-order quantifiers merge.

The guards live over `L.sum Language.order` and the equivalence is required
for *every* linear order on `A`, so this is order-invariant SO-Krom
definability. -/
def SigmaSOKromDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ (B : SOBlock) (k : ℕ) (prog : KromProgram (L.sum Language.order) B k),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ ∃ ρ : B.Assignment A, prog.Holds ρ

end Lax485149.KromFragment
end

-- Lax485149.ClassNL
section
namespace Lax485149.ClassNL

open Lax904597.Problems Lax904597.Classes Lax485149.Complement Lax485149.KromFragment

/-- **NL**: the class of the SO-Krom definable problems, with cofinal
hardness. -/
def NL : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSOKromDefinable P

end Lax485149.ClassNL
end

-- Lax485149.FirstOrderDefinability
section
namespace Lax485149
end Lax485149

namespace Lax485149.FirstOrderDefinability
end Lax485149.FirstOrderDefinability
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

-- Lax895169.BitPredicate
section
namespace Lax895169.BitPredicate.prefixHolds
end Lax895169.BitPredicate.prefixHolds

namespace Lax895169.BitPredicate

/-- The rank of an element of a finite linear order: the number of its strict
predecessors. -/
noncomputable def orank {A : Type} [LinearOrder A] (z : A) : ℕ :=
  {y : A | y < z}.ncard

end Lax895169.BitPredicate
end

-- Lax895169.ArithmeticLogic
section
namespace Lax895169.ArithmeticLogic

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the arithmetic vocabulary. -/
inductive arithRel : ℕ → Type
  /-- `le x y`: the rank of `x` is at most the rank of `y`, i.e., `x ≤ y`. -/
  | le : arithRel 2
  /-- `plus x y z`: the ranks satisfy `orank x + orank y = orank z`. -/
  | plus : arithRel 3
  /-- `times x y z`: the ranks satisfy `orank x * orank y = orank z`. -/
  | times : arithRel 3
  deriving DecidableEq

/-- The relational vocabulary of the numeric predicates: a linear order and the
graphs of addition and multiplication of ranks. Interpreted canonically on every
finite linear order by `arithStructure`. -/
def arith : Language :=
  ⟨fun _ => Empty, arithRel⟩

instance instIsRelationalArith : IsRelational arith := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Structures

variable (A : Type) [LinearOrder A] [Finite A]

/-- **The numeric predicates of a finite linear order**: `≤` is the order, and
`plus`/`times` are the graphs of addition and multiplication of ranks. Both are
truncated: a value that is not the rank of an element of `A` is not related to
anything. -/
instance arithStructure : arith.Structure A where
  funMap f := isEmptyElim f
  RelMap {n} R :=
    match n, R with
    | _, .le => fun x => x 0 ≤ x 1
    | _, .plus => fun x => orank (x 0) + orank (x 1) = orank (x 2)
    | _, .times => fun x => orank (x 0) * orank (x 1) = orank (x 2)

end Structures

open FirstOrder

open Language

/-- A decision problem is **AC⁰ definable** if a single sentence over the
arithmetic expansion of its vocabulary decides it on nonempty finite ordered
structures. The equivalence is required for *every* linear order, so the notion
is order-invariant: the sentence sees `≤`, `+` and `×`, the problem does not.
There is no order-free variant: the numeric predicates are computed from the
order, so without one there is nothing for them to mean. -/
def AC0Definable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ φ : (L.sum arith).Sentence,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ A ⊨ φ

end Lax895169.ArithmeticLogic
end

-- Lax895169.BitLogic
section
namespace Lax895169.BitLogic
end Lax895169.BitLogic

namespace Lax895169.BitLogic.BitAtom
end Lax895169.BitLogic.BitAtom

namespace Lax895169.BitLogic.BitKernel
end Lax895169.BitLogic.BitKernel

namespace Lax895169.BitLogic.BitSentence
end Lax895169.BitLogic.BitSentence

namespace Lax895169.BitLogic.BitAtom.Holds
end Lax895169.BitLogic.BitAtom.Holds

namespace Lax895169.BitLogic.BitAtom.bit
end Lax895169.BitLogic.BitAtom.bit

namespace Lax895169.BitLogic.BitAtom.le
end Lax895169.BitLogic.BitAtom.le

namespace Lax895169.BitLogic.BitAtom.plus
end Lax895169.BitLogic.BitAtom.plus

namespace Lax895169.BitLogic.BitAtom.rel
end Lax895169.BitLogic.BitAtom.rel

namespace Lax895169.BitLogic.BitKernel.Holds
end Lax895169.BitLogic.BitKernel.Holds

namespace Lax895169.BitLogic.BitKernel.and
end Lax895169.BitLogic.BitKernel.and

namespace Lax895169.BitLogic.BitKernel.atom
end Lax895169.BitLogic.BitKernel.atom

namespace Lax895169.BitLogic.BitKernel.not
end Lax895169.BitLogic.BitKernel.not

namespace Lax895169.BitLogic.BitKernel.or
end Lax895169.BitLogic.BitKernel.or

namespace Lax895169.BitLogic.BitKernel.tt
end Lax895169.BitLogic.BitKernel.tt
end

-- Lax895169.LogTimeMachines
section
namespace Lax895169.LogTimeMachines
end Lax895169.LogTimeMachines

namespace Lax895169.LogTimeMachines.BaseTest
end Lax895169.LogTimeMachines.BaseTest

namespace Lax895169.LogTimeMachines.BitExpr
end Lax895169.LogTimeMachines.BitExpr

namespace Lax895169.LogTimeMachines.LTMachine
end Lax895169.LogTimeMachines.LTMachine

namespace Lax895169.LogTimeMachines.Sweep
end Lax895169.LogTimeMachines.Sweep

namespace Lax895169.LogTimeMachines.BaseTest.Holds
end Lax895169.LogTimeMachines.BaseTest.Holds

namespace Lax895169.LogTimeMachines.BaseTest.and
end Lax895169.LogTimeMachines.BaseTest.and

namespace Lax895169.LogTimeMachines.BaseTest.bit
end Lax895169.LogTimeMachines.BaseTest.bit

namespace Lax895169.LogTimeMachines.BaseTest.not
end Lax895169.LogTimeMachines.BaseTest.not

namespace Lax895169.LogTimeMachines.BaseTest.or
end Lax895169.LogTimeMachines.BaseTest.or

namespace Lax895169.LogTimeMachines.BaseTest.query
end Lax895169.LogTimeMachines.BaseTest.query

namespace Lax895169.LogTimeMachines.BaseTest.sweep
end Lax895169.LogTimeMachines.BaseTest.sweep

namespace Lax895169.LogTimeMachines.BitExpr.and
end Lax895169.LogTimeMachines.BitExpr.and

namespace Lax895169.LogTimeMachines.BitExpr.eval
end Lax895169.LogTimeMachines.BitExpr.eval

namespace Lax895169.LogTimeMachines.BitExpr.ff
end Lax895169.LogTimeMachines.BitExpr.ff

namespace Lax895169.LogTimeMachines.BitExpr.not
end Lax895169.LogTimeMachines.BitExpr.not

namespace Lax895169.LogTimeMachines.BitExpr.or
end Lax895169.LogTimeMachines.BitExpr.or

namespace Lax895169.LogTimeMachines.BitExpr.tt
end Lax895169.LogTimeMachines.BitExpr.tt

namespace Lax895169.LogTimeMachines.BitExpr.var
end Lax895169.LogTimeMachines.BitExpr.var

namespace Lax895169.LogTimeMachines.Sweep.state
end Lax895169.LogTimeMachines.Sweep.state
end

-- Lax895169.ACZeroInLogSpace
section
namespace Lax895169.ACZeroInLogSpace

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Classes

open Lax485149.Complement Lax485149.FirstOrderDefinability Lax485149.DeterministicTransitiveClosure

open Lax485149.ClassNL Lax485149.ClassL

open Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME

open Lax895169.BitPredicate Lax895169.ArithmeticLogic Lax895169.BitLogic Lax895169.LogTimeMachines

/-- Every AC⁰ definable problem is in NL. -/
axiom ac0Definable_mem_NL : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  AC0Definable P → NL.Mem P

end Lax895169.ACZeroInLogSpace
end
