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
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
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

end Shorthands

variable (A : Type) [twoGraphs.Structure A]

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.SubgraphIso
end
