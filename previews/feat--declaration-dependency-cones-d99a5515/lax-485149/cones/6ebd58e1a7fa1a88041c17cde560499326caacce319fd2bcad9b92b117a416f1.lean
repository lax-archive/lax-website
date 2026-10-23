-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Relation
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
namespace Lax485149.Complement

open Lax904597.Problems

open FirstOrder

open Language

/-- The complement of a decision problem: its yes-instances are the
no-instances of `P`. -/
def DecisionProblem.compl {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    DecisionProblem L where
  Holds := fun A inst => ¬@DecisionProblem.Holds L _ P A inst
  iso_invariant := fun e => not_congr (P.iso_invariant e)

end Lax485149.Complement
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

end Lax485149.TransitiveClosure
end

-- Lax485149.DeterministicTransitiveClosure
section
namespace Lax485149.DeterministicTransitiveClosure

open Lax485149.TransitiveClosure Lax904597.Problems

open FirstOrder

open Language Structure

namespace TCSpec

section Det

variable {L : Language.{0, 0}} (spec : TCSpec L)

/-- The renaming used by the uniqueness clause: the transition formula is
re-read with its first tuple still the current one and its second tuple the
freshly quantified `z̄`. -/
def detVar : Fin spec.k ⊕ Fin spec.k → (Fin spec.k ⊕ Fin spec.k) ⊕ Fin spec.k :=
  Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr

open Classical in
/-- **The determinized transition formula** at a pair of modes: this step, and
no other step out of the current node. The competing successors are quantified
as a tuple `z̄` and a *mode* `m'`; the mode is compared statically, so the
uniqueness clause has one conjunct per mode, asserting `z̄ = ȳ` at the intended
one and refuting the step at every other. -/
noncomputable def detStep (m n : spec.Mode) :
    (L.sum Language.order).Formula (Fin spec.k ⊕ Fin spec.k) :=
  spec.step m n ⊓
    Formula.iInf fun m' : spec.Mode =>
      Formula.iAlls (Fin spec.k)
        (((spec.step m m').relabel (detVar spec)).imp
          (if m' = n then
            Formula.iInf fun i : Fin spec.k =>
              Term.equal (Term.var (Sum.inr i)) (Term.var (Sum.inl (Sum.inr i)))
          else ⊥))

/-- **The deterministic reading of a specification**: the same modes, arity and
endpoints, with the transition formula replaced by its determinization.

Marked `@[reducible]` so that the modes and the arity of `spec.det` are those of
`spec` transparently: a node of the deterministic reading *is* a node, and
numerals at `Fin spec.det.k` elaborate as they do at `Fin spec.k`. -/
@[reducible]
noncomputable def det : TCSpec L where
  Mode := spec.Mode
  k := spec.k
  step := detStep spec
  src := spec.src
  tgt := spec.tgt

end Det

end TCSpec

/-- A decision problem is *FO(DTC) definable* if, on nonempty finite *ordered*
structures, it is defined by a single **deterministic** transitive closure:
there is a `TCSpec` whose accepting nodes are reachable from its starting
nodes *along its determinization* exactly on the yes-instances.

As for `TCDefinable`, the equivalence is required for every linear order on
the universe, so this is order-invariant FO(DTC) definability. -/
def DTCDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : TCSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ (TCSpec.det spec).Accepts A

end Lax485149.DeterministicTransitiveClosure
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

open Lax904597.Problems Lax904597.Classes Lax485149.Complement

open Lax485149.TransitiveClosure Lax485149.DeterministicTransitiveClosure

/-- **coL**: the problems whose complement is in L. -/
def coLOGSPACE : ComplexityClass :=
  ComplexityClass.ofMem fun P => DTCDefinable (DecisionProblem.compl P)

end Lax485149.ClassL
end
