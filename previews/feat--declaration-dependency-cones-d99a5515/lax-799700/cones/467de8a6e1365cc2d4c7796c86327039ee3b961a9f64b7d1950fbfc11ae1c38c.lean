-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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

-- Lax799700.Problems
section
namespace Lax799700.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax799700.Problems
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

-- Lax799700.ThreeDimMatching
section
namespace Lax799700.ThreeDimMatching

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive tripleSysRel : ℕ → Type where
/-- `xEl a`: `a` belongs to the first class. -/
  | xEl : tripleSysRel 1
/-- `yEl a`: `a` belongs to the second class. -/
  | yEl : tripleSysRel 1
/-- `zEl a`: `a` belongs to the third class. -/
  | zEl : tripleSysRel 1
/-- `trip a b c`: `(a, b, c)` is one of the available triples. -/
  | trip : tripleSysRel 3
  deriving DecidableEq

/-- The relational language of triple systems: three marked classes and a
ternary relation. -/
def tripleSys : FirstOrder.Language :=
  ⟨fun _ => Empty, tripleSysRel⟩

instance instIsRelationalTripleSys : FirstOrder.Language.IsRelational tripleSys := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `xEl a`: `a` belongs to the first class. -/
abbrev tsXEl : tripleSys.Relations 1 :=
  .xEl

/-- `yEl a`: `a` belongs to the second class. -/
abbrev tsYEl : tripleSys.Relations 1 :=
  .yEl

/-- `zEl a`: `a` belongs to the third class. -/
abbrev tsZEl : tripleSys.Relations 1 :=
  .zEl

/-- `trip a b c`: `(a, b, c)` is one of the available triples. -/
abbrev tsTrip : tripleSys.Relations 3 :=
  .trip

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [tripleSys.Structure A]

/-- `xEl a`: `a` belongs to the first class.  -/
def TSXEl {A : Type} [tripleSys.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tsXEl ![a0]

/-- `yEl a`: `a` belongs to the second class.  -/
def TSYEl {A : Type} [tripleSys.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tsYEl ![a0]

/-- `zEl a`: `a` belongs to the third class.  -/
def TSZEl {A : Type} [tripleSys.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tsZEl ![a0]

/-- `trip a b c`: `(a, b, c)` is one of the available triples.  -/
def TSTrip {A : Type} [tripleSys.Structure A] (a0 : A) (a1 : A) (a2 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tsTrip ![a0, a1, a2]

end Shorthands

section Matching

variable {A : Type}

/-- A **matching**: a set of triples, taken from `T` and lying in the three
classes, covering every marked element exactly once. -/
def IsMatchingOn (X Y Z : A → Prop) (T : A → A → A → Prop) (M : A → A → A → Prop) : Prop :=
  (∀ x y z, M x y z → T x y z ∧ X x ∧ Y y ∧ Z z) ∧
    (∀ x, X x → ∃ y z, M x y z) ∧ (∀ y, Y y → ∃ x z, M x y z) ∧
    (∀ z, Z z → ∃ x y, M x y z) ∧
    (∀ x y z y' z', M x y z → M x y' z' → y = y' ∧ z = z') ∧
    (∀ x y z x' z', M x y z → M x' y z' → x = x' ∧ z = z') ∧
    ∀ x y z x' y', M x y z → M x' y' z → x = x' ∧ y = y'

end Matching

section Problem

variable (A : Type) [tripleSys.Structure A]

/-- A triple system is a yes-instance when some subset of its triples covers
each marked element exactly once. -/
def HasThreeDimMatching : Prop :=
  Finite A ∧ ∃ M : A → A → A → Prop,
    IsMatchingOn (TSXEl (A := A)) TSYEl TSZEl TSTrip M

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The problem ThreeDimMatching: does the structure satisfy `HasThreeDimMatching`? -/
def ThreeDimMatching : DecisionProblem Lax799700.ThreeDimMatching.tripleSys :=
  DecisionProblem.ofPred HasThreeDimMatching

/-- The yes-instances of ThreeDimMatching are exactly the structures
satisfying `HasThreeDimMatching`. -/
axiom threeDimMatching_iff : ∀ (A : Type) [Lax799700.ThreeDimMatching.tripleSys.Structure A], ThreeDimMatching A ↔ HasThreeDimMatching A

end Lax799700.ThreeDimMatching
end
