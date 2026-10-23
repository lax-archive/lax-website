-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics

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

variable (A) in
/-- A node of the walk: a mode together with a `k`-tuple of elements. -/
abbrev Node : Type := spec.Mode × (Fin spec.k → A)

/-- One step of the walk: the transition formula of the two modes, read with
the current tuple on the left and the next one on the right. -/
def Step (a b : spec.Node A) : Prop :=
  (spec.step a.1 b.1).Realize (Sum.elim a.2 b.2)

/-- Reachability in the walk: the reflexive-transitive closure of
`TCSpec.Step`. -/
abbrev Reach : spec.Node A → spec.Node A → Prop :=
  Relation.ReflTransGen spec.Step

/-- A node is a starting node when its tuple satisfies the source formula of
its mode. -/
def IsSrc (a : spec.Node A) : Prop := (spec.src a.1).Realize a.2

/-- A node is accepting when its tuple satisfies the target formula of its
mode. -/
def IsTgt (a : spec.Node A) : Prop := (spec.tgt a.1).Realize a.2

variable (A) in
/-- The structure is accepted: some accepting node is reachable from some
starting node. -/
def Accepts : Prop :=
  ∃ u v : spec.Node A, spec.IsSrc u ∧ spec.IsTgt v ∧ spec.Reach u v

end Semantics

end TCSpec

/-- A decision problem is *FO(TC) definable* if, on nonempty finite *ordered*
structures, it is defined by a single transitive closure: there is a `TCSpec`
whose accepting tuples are reachable from its starting tuples exactly on the
yes-instances.

The equivalence is required for *every* linear order on the universe, so this
is order-invariant FO(TC) definability: the problem itself does not see the
order, while the transition and endpoint formulas may. -/
def TCDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : TCSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.Accepts A

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

-- Lax485149.ClassL
section
namespace Lax485149.ClassL
end Lax485149.ClassL
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

-- Lax485149.KromFragment
section
namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax485149.KromFragment.KromClause
end Lax485149.KromFragment.KromClause

namespace Lax485149.KromFragment.KromLit
end Lax485149.KromFragment.KromLit

namespace Lax485149.KromFragment.KromProgram
end Lax485149.KromFragment.KromProgram
end

-- Lax485149.ClassNL
section
namespace Lax485149.ClassNL
end Lax485149.ClassNL
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

-- Lax485149.Reachability
section
namespace Lax485149.Reachability

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open Lax904597.Problems Lax485149.Problems Lax485149.Complement

/-- The relation symbols of graphs with marked sources and targets. -/
inductive stGraphRel : ℕ → Type where
  /-- `edge a b`: there is an edge from `a` to `b`. -/
  | edge : stGraphRel 2
  /-- `source a`: the vertex `a` is a marked source. -/
  | source : stGraphRel 1
  /-- `target a`: the vertex `a` is a marked target. -/
  | target : stGraphRel 1
  deriving DecidableEq

/-- The relational vocabulary of directed graphs with marked sources and
targets. -/
def stGraph : Language :=
  ⟨fun _ => Empty, stGraphRel⟩

instance instIsRelationalStGraph : IsRelational stGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

end Lax485149.Reachability
end

-- Lax485149.DeterministicReachability
section
namespace Lax485149.DeterministicReachability
end Lax485149.DeterministicReachability
end

-- Lax485149.FirstOrderDefinability
section
namespace Lax485149
end Lax485149

namespace Lax485149.FirstOrderDefinability
end Lax485149.FirstOrderDefinability
end

-- Lax485149.HeadAutomata
section
namespace Lax485149.HeadAutomata

open FirstOrder

open Language Structure

/-- What a head may do in one step: stay where it is, jump to an end of the
order, copy another head, or step to the immediate successor or predecessor of
another head. All of it is definable from the order, which is what lets a
transition become a first-order formula. -/
inductive HeadMove (k : ℕ) where
  /-- Stay on the current element. -/
  | stay : HeadMove k
  /-- Jump to the least element. -/
  | toMin : HeadMove k
  /-- Jump to the greatest element. -/
  | toMax : HeadMove k
  /-- Copy the position of head `i`. -/
  | copy (i : Fin k) : HeadMove k
  /-- Move to the immediate successor of head `i` (disabled at the greatest
  element, which is how a head runs off the end). -/
  | succ (i : Fin k) : HeadMove k
  /-- Move to the immediate predecessor of head `i` (disabled at the least
  element). -/
  | pred (i : Fin k) : HeadMove k
  deriving DecidableEq

namespace HeadMove

variable {k : ℕ} {A : Type} [LinearOrder A]

/-- The semantics of a move: where head `j` may be after it, the current heads
being `x`. -/
def Holds (mv : HeadMove k) (x : Fin k → A) (j : Fin k) (y : A) : Prop :=
  match mv with
  | .stay => y = x j
  | .toMin => ∀ b : A, y ≤ b
  | .toMax => ∀ b : A, b ≤ y
  | .copy i => y = x i
  | .succ i => x i < y ∧ ∀ a : A, ¬(x i < a ∧ a < y)
  | .pred i => y < x i ∧ ∀ a : A, ¬(y < a ∧ a < x i)

end HeadMove

/-- **A two-way `k`-head automaton over `L`-structures**: a finite control, a
finite list of quantifier-free tests of the head positions, and, per state and
per outcome of those tests, a list of possible transitions – a new state and one
move per head. No work tape: all the storage is in the `k` heads. -/
structure HeadAutomaton (L : Language.{0, 0}) (k : ℕ) where
  /-- The control states. -/
  State : Type
  /-- The control is finite: that is what makes this a machine. -/
  [stateFinite : Finite State]
  /-- The initial state. -/
  start : State
  /-- The accepting states. -/
  accept : State → Bool
  /-- What the control reads at each step, indexed by a finite type. -/
  TestIx : Type
  /-- Finitely many tests: a control that could read unboundedly many facts
  would not be a finite control. -/
  [testFinite : Finite TestIx]
  /-- The tests: what the control sees of the current head positions. -/
  test : TestIx → (L.sum Language.order).Formula (Fin k)
  /-- **The tests are quantifier-free.** The control may compare its heads and
  look at the relations holding between them, and nothing else; a quantified
  test would make the model first-order logic in disguise. -/
  test_qf : ∀ i, (test i).IsQF
  /-- The transitions available in a state, at a given outcome of the tests:
  a new state and a move for each head. Nondeterminism is the length of this
  list. -/
  trans : State → (TestIx → Bool) → List (State × (Fin k → HeadMove k))

attribute [instance] HeadAutomaton.stateFinite HeadAutomaton.testFinite

namespace HeadAutomaton

variable {L : Language.{0, 0}} {k : ℕ} (M : HeadAutomaton L k) {A : Type} [L.Structure A]
  [LinearOrder A]

/-- A configuration: a control state together with the positions of the heads. -/
abbrev Config (A : Type) : Type := M.State × (Fin k → A)

open Classical in
/-- What the control reads at a configuration: the truth values of its tests. -/
noncomputable def reading (x : Fin k → A) : M.TestIx → Bool :=
  fun i => decide ((M.test i).Realize x)

/-- One step of the automaton: some transition available at the current state
and reading leads to the new state, each head moving as it prescribes. -/
def Step (a b : M.Config A) : Prop :=
  ∃ p ∈ M.trans a.1 (M.reading a.2), p.1 = b.1 ∧ ∀ j, (p.2 j).Holds a.2 j (b.2 j)

/-- The automaton accepts the structure when an accepting state is reachable
from an initial configuration – the initial state with every head on the least
element. -/
def Accepts (A : Type) [L.Structure A] [LinearOrder A] : Prop :=
  ∃ c₀ c : M.Config A, (c₀.1 = M.start ∧ ∀ j, ∀ b : A, c₀.2 j ≤ b) ∧
    Relation.ReflTransGen M.Step c₀ c ∧ M.accept c.1 = true

end HeadAutomaton

end Lax485149.HeadAutomata
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

-- Lax485149.TwoSat
section
namespace Lax485149.TwoSat
end Lax485149.TwoSat

namespace Lax485149.TwoSat.SatOcc
end Lax485149.TwoSat.SatOcc
end

-- Lax485149.NLByAutomata
section
namespace Lax485149.NLByAutomata

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Sat

open Lax485149.Problems Lax485149.Complement Lax485149.SecondOrderAtoms Lax485149.KromFragment

open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure

open Lax485149.FirstOrderDefinability Lax485149.HeadAutomata Lax485149.Reachability

open Lax485149.DeterministicReachability Lax485149.TwoSat Lax485149.ClassNL Lax485149.ClassL

/-- FO(TC) definability is acceptance by a two-way multihead automaton. -/
axiom tcDefinable_iff_automaton : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  TCDefinable P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ M.Accepts A

end Lax485149.NLByAutomata
end
