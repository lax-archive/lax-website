-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sort
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
import Mathlib.Tactic.FinCases
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

/-- A counting problem is parsimoniously complete for a class when it belongs
to it and is parsimoniously hard for it. -/
def CountingClass.ParsimoniousComplete (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) : Prop :=
  K.Mem C ∧ K.ParsimoniousHard C

end Lax366625.CountingClasses
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

-- Lax799700.SetFamily
section
namespace Lax799700.SetFamily

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive setSystemRel : ℕ → Type where
/-- `elem a`: the element `a` belongs to the ground set. -/
  | elem : setSystemRel 1
/-- `fam a`: the element `a` is one of the sets of the family. -/
  | fam : setSystemRel 1
/-- `mem a b`: the ground element `a` belongs to the set `b`. -/
  | mem : setSystemRel 2
/-- `marked a`: the element `a` belongs to the marked set. -/
  | marked : setSystemRel 1
  deriving DecidableEq

/-- The relational language of set systems: a bipartite incidence structure
between ground elements and sets of a family, together with a marked subset of
the universe whose cardinality serves as threshold. -/
def setSystem : FirstOrder.Language :=
  ⟨fun _ => Empty, setSystemRel⟩

instance instIsRelationalSetSystem : FirstOrder.Language.IsRelational setSystem := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

end Generic

section Problems

section Shorthands

variable {A : Type} [setSystem.Structure A]

end Shorthands

variable (A : Type) [setSystem.Structure A]

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.SetFamily
end

-- Lax859101.CountingAllSets
section
namespace Lax859101
end Lax859101

namespace Lax859101.CountingAllSets
end Lax859101.CountingAllSets
end

-- Lax859101.CountingBipartite
section
namespace Lax859101.CountingBipartite

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive bipGraphRel : ℕ → Type where
/-- `left a`: the vertex `a` is on the left side. -/
  | left : bipGraphRel 1
/-- `edge a b`: there is an edge between `a` and `b`; read for `a` on the
  left and `b` on the right. -/
  | edge : bipGraphRel 2
  deriving DecidableEq

/-- The relational language of bipartite graphs given with their bipartition. -/
def bipGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, bipGraphRel⟩

instance instIsRelationalBipGraph : FirstOrder.Language.IsRelational bipGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [bipGraph.Structure A]

end Shorthands

open Lax366625.CountingProblems

end Lax859101.CountingBipartite
end

-- Lax859101.CountingDnf
section
namespace Lax859101
end Lax859101

namespace Lax859101.CountingDnf
end Lax859101.CountingDnf
end

-- Lax799700.NaeSat
section
namespace Lax799700.NaeSat
end Lax799700.NaeSat
end

-- Lax859101.CountingNaeSat
section
namespace Lax859101
end Lax859101

namespace Lax859101.CountingNaeSat
end Lax859101.CountingNaeSat
end

-- Lax799700.Common
section
namespace Lax799700.Common
end Lax799700.Common

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc
end

-- Lax859101.CountingRestrictedSat
section
namespace Lax859101
end Lax859101

namespace Lax859101.CountingRestrictedSat
end Lax859101.CountingRestrictedSat
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

-- Lax859101.SubtractiveReductions
section
namespace Lax859101.SubtractiveReductions

open Lax366625.CountingProblems Lax366625.WitnessCounting Lax904597.Interpretations

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

open FirstOrder

open Language Structure BoundedFormula

section LexFormulas

variable {L : Language.{0, 0}}

/-- `x = y`, as a formula over the ordered expansion. -/
def oEqF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  Term.equal (Term.var x) (Term.var y)

/-- `x ≤ y`, as a formula over the ordered expansion. -/
def oLeF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- `x < y`, as a formula over the ordered expansion. -/
def oLtF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  oLeF x y ⊓ ∼(oEqF x y)

variable {A : Type} [L.Structure A] [LinearOrder A] {α : Type} {v : α → A}

variable (L) in
/-- Lexicographic comparison of two `d`-tuples (the two arguments of a binary
relation), as a formula over the ordered expansion. -/
noncomputable def lexTupleLeF (d : ℕ) : (L.sum Language.order).Formula (Fin 2 × Fin d) :=
  (Formula.iInf fun i : Fin d => oEqF (0, i) (1, i)) ⊔
    Formula.iSup fun j : Fin d =>
      (Formula.iInf fun i : {i : Fin d // i < j} => oEqF (0, i.1) (1, i.1)) ⊓
        oLtF (0, j) (1, j)

open Classical in
variable (L) in
/-- The full lexicographic comparison of tagged tuples, as a formula over the
ordered expansion: the tags are compared statically. -/
noncomputable def lexLeF {Tag : Type} [LinearOrder Tag] (d : ℕ) (t₁ t₂ : Tag) :
    (L.sum Language.order).Formula (Fin 2 × Fin d) :=
  if t₁ = t₂ then lexTupleLeF L d else if t₁ < t₂ then ⊤ else ⊥

end LexFormulas

section OrdExtend

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational]

variable {T : Type} [LinearOrder T] {d : ℕ}

/-- Extension of an interpretation over an ordered base to one whose target
carries the order vocabulary, interpreted by the lexicographic order on
tagged tuples. -/
noncomputable def FOInterpretation.ordExtend
    (I : FOInterpretation (L₁.sum Language.order) L₂ T d) :
    FOInterpretation (L₁.sum Language.order) (L₂.sum Language.order) T d where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl r => I.relFormula r
    | _, Sum.inr .le => fun t => lexLeF L₁ d (t 0) (t 1)

end OrdExtend

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

/-- The assignment `ρ` is a witness of the kernel `φ` at the instance drawn by
the interpretation `I`, ordered lexicographically. The universe of that
instance is `Tag × A ^ dim` whatever `I` is, so the witnesses at two
interpretations with the same tags and dimension are comparable. -/
def FOInterpretation.WitAt (I : FOInterpretation (L.sum Language.order) L' Tag dim)
    (B : SOBlock) (φ : ((L'.sum Language.order).sum B.lang).Sentence) (A : Type)
    [L.Structure A] [LinearOrder A] (ρ : B.Assignment (Tag × (Fin dim → A))) : Prop :=
  @Sentence.Realize ((L'.sum Language.order).sum B.lang) ((FOInterpretation.ordExtend I).Map A)
    (@sumStructure (L'.sum Language.order) B.lang ((FOInterpretation.ordExtend I).Map A)
      (FOInterpretation.mapStructure (FOInterpretation.ordExtend I) A)
        (B.structure ρ)) φ

end WitAt

/-- A **strong subtractive reduction**: the target is presented as the witness
count of a kernel, two interpretations with the same tags and dimension draw a
subtrahend and a minuend, every witness at the first is a witness at the
second, and the count of the source is the difference of the two counts. -/
structure StrongSubtractiveReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags used by the two interpretations. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty ones. -/
  [tagNonempty : Nonempty Tag]
  /-- Tags are linearly ordered: the order of the drawn instances is the
  lexicographic one. -/
  [tagOrder : LinearOrder Tag]
  /-- The dimension of the two interpretations. -/
  dim : ℕ
  /-- The second-order block of the presentation of the target. -/
  block : SOBlock
  /-- The first-order kernel of the presentation of the target. -/
  kernel : ((L'.sum Language.order).sum block.lang).Sentence
  /-- The target counts the witnesses of its presentation, whatever the linear
  order. -/
  present : ∀ (A : Type) [L'.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    D A = witnessCount block kernel A
  /-- The interpretation drawing the subtrahend. -/
  subtrahend : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- The interpretation drawing the minuend. -/
  minuend : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- Every witness at the subtrahend is a witness at the minuend. -/
  witness_le : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
    (ρ : block.Assignment (Tag × (Fin dim → A))),
    FOInterpretation.WitAt subtrahend block kernel A ρ →
      FOInterpretation.WitAt minuend block kernel A ρ
  /-- The count of the source and the count at the subtrahend add up to the
  count at the minuend. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A + D (subtrahend.Map A) = D (minuend.Map A)

/-- **Subtractive reducibility**, `C ≤ˢ D`: a finite chain of steps, each a
strong subtractive reduction or a relativized ordered parsimonious
reduction. -/
inductive SubtractiveReducible : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational],
    CountingProblem L → CountingProblem L' → Prop
  /-- The empty chain. -/
  | refl {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
      SubtractiveReducible C C
  /-- A strong subtractive step, then a chain. -/
  | strong {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      [L₃.IsRelational] {C : CountingProblem L₁} {D : CountingProblem L₂}
      {E : CountingProblem L₃} (f : StrongSubtractiveReduction C D)
      (h : SubtractiveReducible D E) : SubtractiveReducible C E
  /-- A parsimonious step, then a chain. -/
  | parsimonious {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      [L₃.IsRelational] {C : CountingProblem L₁} {D : CountingProblem L₂}
      {E : CountingProblem L₃} (f : RelOrderedParsimoniousReduction C D)
      (h : SubtractiveReducible D E) : SubtractiveReducible C E

open Lax366625.CountingProblems Lax366625.CountingClasses

/-- A counting problem is **hard** for a class when every problem of the class
reduces to it by a subtractive reduction. -/
def SubtractiveHard (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) : Prop :=
  ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
    K.Mem D → SubtractiveReducible D C

/-- A counting problem is **complete** for a class when it belongs to it and is
hard for it, under subtractive reductions. -/
def SubtractiveComplete (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) : Prop :=
  K.Mem C ∧ SubtractiveHard K C

end Lax859101.SubtractiveReductions
end

-- Lax859101.SubtractiveClosure
section
namespace Lax859101.SubtractiveClosure

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat

open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- A parsimoniously #P-complete problem is #P-complete. -/
axiom subtractiveComplete_sharpP_of_parsimoniousComplete :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
    SharpP.ParsimoniousComplete C → SubtractiveComplete SharpP C

end Lax859101.SubtractiveClosure
end
