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

/-- `isClause c`: the element `c` is a clause. -/
abbrev satIsClause : sat.Relations 1 := .isClause

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev satPosIn : sat.Relations 2 := .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev satNegIn : sat.Relations 2 := .negIn

end Lax904597.Sat
end

-- Lax366625.CountingSat
section
namespace Lax366625.CountingSat

open Lax904597.Sat

open FirstOrder

open Language Structure

section Sat

variable (A : Type) [sat.Structure A]

/-- The element `x` is a variable of the CNF formula: it occurs, positively or
negatively, in some clause. The decision problem does not need the notion –
an element in no clause is harmless – but everything that *counts* assignments
does, and so does any reduction that must not give such an element a truth
value to choose. -/
def SatOccurs (x : A) : Prop :=
  ∃ c : A, RelMap satIsClause ![c] ∧ (RelMap satPosIn ![c, x] ∨ RelMap satNegIn ![c, x])

end Sat

open FirstOrder

open Language Structure

section Models

variable (A : Type) [sat.Structure A]

/-- The set `ν` of true variables is a model of the CNF formula: every clause
contains a true literal, and `ν` consists of variables of the formula. -/
def SatModel (ν : A → Prop) : Prop :=
  (∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)) ∧
  ∀ x : A, ν x → SatOccurs A x

end Models

open Lax366625.CountingProblems

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

open Lax904597.Sat

section Decode

variable {A : Type}

end Decode

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [sat.Structure A]

/-- `c` is a clause. -/
def IsCl (c : A) : Prop := RelMap satIsClause ![c]

/-- `x` occurs positively in `c`. -/
def PosIn (c x : A) : Prop := RelMap satPosIn ![c, x]

/-- `x` occurs negatively in `c`. -/
def NegIn (c x : A) : Prop := RelMap satNegIn ![c, x]

/-- The literal `(x, s)` occurs in the clause `c` (`s = true` for a positive
occurrence). Occurrences are restricted to actual clauses, so that stray
`posIn`/`negIn` facts on non-clause elements do not create gadgets. -/
def OccIn (c x : A) (s : Bool) : Prop := IsCl c ∧ if s then PosIn c x else NegIn c x

end SatOcc

end Lax799700.Common
end

-- Lax859101.CountingRestrictedSat
section
namespace Lax859101.CountingRestrictedSat

open Lax799700.Common Lax904597.Sat

open FirstOrder

open Language Structure

section HornSat

variable (A : Type) [sat.Structure A]

end HornSat

open FirstOrder

open Language Structure

section TwoSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a `Language.sat`-structure has at most two literal
occurrences: among any three occurrences of a clause, two coincide (as signed
occurrences). -/
def WidthAtMostTwo : Prop :=
  ∀ (c : A) (x : Fin 3 → A) (s : Fin 3 → Bool),
    (∀ i, SatOcc.OccIn c (x i) (s i)) → ∃ i j, i ≠ j ∧ x i = x j ∧ s i = s j

end TwoSat

open FirstOrder

open Language Structure

section Sentences

variable {α : Type}

variable {A : Type} [sat.Structure A]

end Sentences

open Lax366625.CountingProblems Lax366625.CountingSat

/-- **#2SAT**, as a counting problem. -/
noncomputable def SharpTwoSAT : CountingProblem Lax904597.Sat.sat :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {ν : A → Prop // WidthAtMostTwo A ∧ SatModel A ν}

end Lax859101.CountingRestrictedSat
end

-- Lax859101.OneCallReductions
section
namespace Lax859101.OneCallReductions

open Lax366625.CountingProblems Lax904597.Relativized

open FirstOrder

open Language Structure

/-- Terms denoting numbers polynomial in the size of the instance: numerals,
definable cardinalities, sums and products. -/
inductive PolyTerm (L : Language.{0, 0}) : Type 1
  /-- A numeral. -/
  | num (k : ℕ) : PolyTerm L
  /-- The number of tagged tuples satisfying their tag's domain formula, i.e.,
  the size of the universe of a relativized interpretation. -/
  | card {Tag : Type} [Finite Tag] {dim : ℕ}
      (J : RelFOInterpretation (L.sum Language.order) Language.empty Tag dim) : PolyTerm L
  /-- A sum. -/
  | add (p q : PolyTerm L) : PolyTerm L
  /-- A product. -/
  | mul (p q : PolyTerm L) : PolyTerm L

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The value of a polynomial term at an ordered structure. -/
noncomputable def eval (A : Type) [L.Structure A] [LinearOrder A] : PolyTerm L → ℕ
  | num k => k
  | card J => Nat.card (J.MapRel A)
  | add p q => p.eval A + q.eval A
  | mul p q => p.eval A * q.eval A

end PolyTerm

/-- The arithmetic applied to the answer of an oracle call: polynomial terms,
powers of two with a polynomial exponent, and the operations `+`, `*`,
truncated `-`, `/` and `%` of the natural numbers. -/
inductive PostTerm (L : Language.{0, 0}) : Type 1
  /-- The answer of the oracle. -/
  | oracle : PostTerm L
  /-- A polynomial term. -/
  | poly (p : PolyTerm L) : PostTerm L
  /-- Two to the power of a polynomial term. -/
  | pow2 (p : PolyTerm L) : PostTerm L
  /-- A sum. -/
  | add (s t : PostTerm L) : PostTerm L
  /-- A product. -/
  | mul (s t : PostTerm L) : PostTerm L
  /-- A truncated difference. -/
  | sub (s t : PostTerm L) : PostTerm L
  /-- A quotient. -/
  | div (s t : PostTerm L) : PostTerm L
  /-- A remainder. -/
  | mod (s t : PostTerm L) : PostTerm L

namespace PostTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The value of a post-processing term at an ordered structure, given the
answer `c` of the oracle. -/
noncomputable def eval (A : Type) [L.Structure A] [LinearOrder A] (c : ℕ) : PostTerm L → ℕ
  | oracle => c
  | poly p => p.eval A
  | pow2 p => 2 ^ p.eval A
  | add s t => s.eval A c + t.eval A c
  | mul s t => s.eval A c * t.eval A c
  | sub s t => s.eval A c - t.eval A c
  | div s t => s.eval A c / t.eval A c
  | mod s t => s.eval A c % t.eval A c

end PostTerm

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-- A one-call counting reduction: a relativized ordered interpretation and a
post-processing term recovering the count of the source from the count of the
interpreted instance. -/
structure OneCallReduction [L.IsRelational] [L'.IsRelational]
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
  /-- The arithmetic applied to the answer of the oracle. -/
  post : PostTerm L
  /-- The count of the source is the post-processed count of the interpreted
  instance, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = post.eval A (D (toRelInterpretation.MapRel A))

open Lax366625.CountingProblems Lax366625.CountingClasses

/-- A counting problem is in the **one-call closure** of a class when it reduces
with one call to a problem of the class. -/
def OneCallMem (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
    Prop :=
  ∃ (L'' : Language.{0, 0}) (_ : L''.IsRelational) (D : CountingProblem L''),
    K.Mem D ∧ Nonempty (OneCallReduction C D)

/-- A counting problem is **one-call hard** for a class when every problem of the
class reduces to it with one call. -/
def OneCallHard (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
    Prop :=
  ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
    K.Mem D → Nonempty (OneCallReduction D C)

/-- A counting problem is **one-call complete** for a class when it is in the
one-call closure of the class and one-call hard for it. -/
def OneCallComplete (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) : Prop :=
  OneCallMem K C ∧ OneCallHard K C

end Lax859101.OneCallReductions
end

-- Lax859101.SubtractiveReductions
section
namespace Lax859101
end Lax859101

namespace Lax859101.SubtractiveReductions
end Lax859101.SubtractiveReductions

namespace Lax859101.SubtractiveReductions.FOInterpretation
end Lax859101.SubtractiveReductions.FOInterpretation

namespace Lax859101.SubtractiveReductions.StrongSubtractiveReduction
end Lax859101.SubtractiveReductions.StrongSubtractiveReduction

namespace Lax859101.SubtractiveReductions.SubtractiveReducible
end Lax859101.SubtractiveReductions.SubtractiveReducible

namespace Lax859101.SubtractiveReductions.FOInterpretation.ordExtend
end Lax859101.SubtractiveReductions.FOInterpretation.ordExtend
end

-- Lax859101.RestrictedSatComplete
section
namespace Lax859101.RestrictedSatComplete

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat

open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- #2SAT is one-call #P-complete. -/
axiom sharpTwoSat_sharpP_oneCallComplete :
  OneCallComplete SharpP SharpTwoSAT

end Lax859101.RestrictedSatComplete
end
