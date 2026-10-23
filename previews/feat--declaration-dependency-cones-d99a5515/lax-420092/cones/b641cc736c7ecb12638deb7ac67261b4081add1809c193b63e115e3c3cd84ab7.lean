-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

-- Lax420092.QueryDatabases
section
namespace Lax420092
end Lax420092

namespace Lax420092.QueryDatabases
end Lax420092.QueryDatabases

namespace Lax420092.QueryDatabases.queryDbRel
end Lax420092.QueryDatabases.queryDbRel

namespace Lax420092.QueryDatabases.queryDbRel.atom
end Lax420092.QueryDatabases.queryDbRel.atom

namespace Lax420092.QueryDatabases.queryDbRel.fact
end Lax420092.QueryDatabases.queryDbRel.fact

namespace Lax420092.QueryDatabases.queryDbRel.isVar
end Lax420092.QueryDatabases.queryDbRel.isVar
end

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

-- Lax420092.Evaluation
section
namespace Lax420092.Evaluation
end Lax420092.Evaluation
end

-- Lax420092.QueryPairs
section
namespace Lax420092.QueryPairs

open Lax420092.Evaluation

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive queryPairRel : ℕ → Type where
/-- `leftVar x`: the element `x` is a variable of the left query. -/
  | leftVar : queryPairRel 1
/-- `rightVar x`: the element `x` is a variable of the right query. -/
  | rightVar : queryPairRel 1
/-- `leftAtom x y`: the left query contains the atom `E(x, y)`. -/
  | leftAtom : queryPairRel 2
/-- `rightAtom x y`: the right query contains the atom `E(x, y)`. -/
  | rightAtom : queryPairRel 2
  deriving DecidableEq

/-- The relational language of pairs of conjunctive queries over a shared
universe of variables and constants. -/
def queryPair : FirstOrder.Language :=
  ⟨fun _ => Empty, queryPairRel⟩

/-- `leftAtom x y`: the left query contains the atom `E(x, y)`. -/
abbrev qpLeftAtom : queryPair.Relations 2 :=
  .leftAtom

open FirstOrder

open Language Structure BoundedFormula

section PairShorthands

variable {A : Type} [queryPair.Structure A]

/-- `E(x, y)` is an atom of the left query. -/
def LAtom (x y : A) : Prop := RelMap qpLeftAtom ![x, y]

end PairShorthands

open Lax904597.Problems Lax799700.Problems

end Lax420092.QueryPairs
end
