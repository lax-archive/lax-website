-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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

-- Lax799700.SubgraphIso
section
namespace Lax799700.SubgraphIso

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive twoGraphsRel : ℕ → Type where
/-- `patV a`: `a` is a vertex of the pattern graph. -/
  | patV : twoGraphsRel 1
/-- `hostV a`: `a` is a vertex of the host graph. -/
  | hostV : twoGraphsRel 1
/-- `patE a b`: there is an edge of the pattern from `a` to `b`. -/
  | patE : twoGraphsRel 2
/-- `hostE a b`: there is an edge of the host from `a` to `b`. -/
  | hostE : twoGraphsRel 2
  deriving DecidableEq

/-- The relational language of pattern-and-host graphs: two graphs sharing a
universe, each with its own vertex mark and adjacency relation. -/
def twoGraphs : FirstOrder.Language :=
  ⟨fun _ => Empty, twoGraphsRel⟩

instance instIsRelationalTwoGraphs : FirstOrder.Language.IsRelational twoGraphs := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `patV a`: `a` is a vertex of the pattern graph. -/
abbrev tgPatV : twoGraphs.Relations 1 :=
  .patV

/-- `hostV a`: `a` is a vertex of the host graph. -/
abbrev tgHostV : twoGraphs.Relations 1 :=
  .hostV

/-- `patE a b`: there is an edge of the pattern from `a` to `b`. -/
abbrev tgPatE : twoGraphs.Relations 2 :=
  .patE

/-- `hostE a b`: there is an edge of the host from `a` to `b`. -/
abbrev tgHostE : twoGraphs.Relations 2 :=
  .hostE

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Generic

variable {A : Type}

/-- Some map sends the `PV`-vertices injectively into the `HV`-vertices,
carrying `PE`-edges to `HE`-edges: an injective homomorphism of the pattern
into the host. -/
def SubgraphIsoOn (PV HV : A → Prop) (PE HE : A → A → Prop) : Prop :=
  ∃ f : A → A, (∀ x, PV x → HV (f x)) ∧
    (∀ x y, PV x → PV y → f x = f y → x = y) ∧
    ∀ x y, PV x → PV y → PE x y → HE (f x) (f y)

end Generic

section Problem

section Shorthands

variable {A : Type} [twoGraphs.Structure A]

/-- `patV a`: `a` is a vertex of the pattern graph.  -/
def TGPatV {A : Type} [twoGraphs.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgPatV ![a0]

/-- `hostV a`: `a` is a vertex of the host graph.  -/
def TGHostV {A : Type} [twoGraphs.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgHostV ![a0]

/-- `patE a b`: there is an edge of the pattern from `a` to `b`.  -/
def TGPatE {A : Type} [twoGraphs.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgPatE ![a0, a1]

/-- `hostE a b`: there is an edge of the host from `a` to `b`.  -/
def TGHostE {A : Type} [twoGraphs.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgHostE ![a0, a1]

end Shorthands

variable (A : Type) [twoGraphs.Structure A]

/-- The host graph contains a subgraph isomorphic to the pattern graph.
(Finiteness of the universe is required only for uniformity with the rest of
the catalog; the property itself makes sense in general.) -/
def HasSubgraphIso : Prop :=
  Finite A ∧ SubgraphIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The problem SubgraphIso: does the structure satisfy `HasSubgraphIso`? -/
def SubgraphIso : DecisionProblem Lax799700.SubgraphIso.twoGraphs :=
  DecisionProblem.ofPred HasSubgraphIso

/-- The yes-instances of SubgraphIso are exactly the structures satisfying
`HasSubgraphIso`. -/
axiom subgraphIso_iff : ∀ (A : Type) [Lax799700.SubgraphIso.twoGraphs.Structure A], SubgraphIso A ↔ HasSubgraphIso A

end Lax799700.SubgraphIso
end
