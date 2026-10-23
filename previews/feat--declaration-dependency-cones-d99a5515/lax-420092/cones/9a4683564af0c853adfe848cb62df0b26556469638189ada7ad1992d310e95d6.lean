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
namespace Lax420092.QueryDatabases

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive queryDbRel : ℕ → Type where
/-- `isVar x`: the element `x` is a variable of the query. -/
  | isVar : queryDbRel 1
/-- `atom x y`: the query contains the atom `E(x, y)` (its arguments are
  variables or constants). -/
  | atom : queryDbRel 2
/-- `fact a b`: the database contains the fact `E(a, b)`. -/
  | fact : queryDbRel 2
  deriving DecidableEq

/-- The relational language of BCQ evaluation instances: a query and a
database over a shared universe, with a unary predicate singling out the
query variables and binary predicates for query atoms and database facts. -/
def queryDb : FirstOrder.Language :=
  ⟨fun _ => Empty, queryDbRel⟩

/-- `isVar x`: the element `x` is a variable of the query. -/
abbrev qdbIsVar : queryDb.Relations 1 :=
  .isVar

open FirstOrder

open Language Structure BoundedFormula

section EvalShorthands

variable {A : Type} [queryDb.Structure A]

/-- `x` is a variable of the query. -/
def QVar (x : A) : Prop := RelMap qdbIsVar ![x]

end EvalShorthands

end Lax420092.QueryDatabases
end
