-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Basic
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

end DecisionProblem

end Lax904597.Problems
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

-- Lax904597.Interpretations
section
namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Interpretations.FOInterpretation
end Lax904597.Interpretations.FOInterpretation

namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.Relativized.RelFOInterpretation
end Lax904597.Relativized.RelFOInterpretation

namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction
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

-- Lax604544.Degrees
section
namespace Lax604544
end Lax604544

namespace Lax604544.Degrees
end Lax604544.Degrees
end

-- Lax604544.RelationIsomorphism
section
namespace Lax604544.RelationIsomorphism

section Generic

variable {A : Type}

/-- Some map is a bijection of the `PV`-vertices onto the `HV`-vertices
carrying `PE`-edges to `HE`-edges *and back*: an isomorphism of the two marked
graphs. -/
def RelIsoOn (PV HV : A → Prop) (PE HE : A → A → Prop) : Prop :=
  ∃ f : A → A, (∀ x, PV x → HV (f x)) ∧
    (∀ x y, PV x → PV y → f x = f y → x = y) ∧
    (∀ y, HV y → ∃ x, PV x ∧ f x = y) ∧
    ∀ x y, PV x → PV y → (PE x y ↔ HE (f x) (f y))

end Generic

end Lax604544.RelationIsomorphism
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

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.SubgraphIso
end

-- Lax604544.GraphIsomorphism
section
namespace Lax604544.GraphIsomorphism

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Classes Lax485149.Problems Lax799700.SubgraphIso

open Lax604544.RelationIsomorphism Lax604544.Degrees

section Problem

variable (A : Type) [twoGraphs.Structure A]

/-- The two marked graphs of the instance are isomorphic. -/
def HasDigraphIso : Prop :=
  Finite A ∧ RelIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE

end Problem

section Generic

variable {A : Type}

end Generic

section Problem

variable (A : Type) [twoGraphs.Structure A]

end Problem

/-- Digraph Isomorphism: are the two marked directed graphs of the instance
isomorphic? -/
def DigraphIso : DecisionProblem twoGraphs :=
  DecisionProblem.ofPred fun A _ => HasDigraphIso A

end Lax604544.GraphIsomorphism
end
