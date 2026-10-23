-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax271696.CliqueExpr
section
namespace Lax271696.CliqueExpr.Valid
end Lax271696.CliqueExpr.Valid

namespace Lax271696.CliqueExpr.ValidFor
end Lax271696.CliqueExpr.ValidFor

namespace Lax271696.CliqueExpr.cls
end Lax271696.CliqueExpr.cls

namespace Lax271696.CliqueExpr.leafIds
end Lax271696.CliqueExpr.leafIds

namespace Lax271696.CliqueExpr

variable {n k : ℕ}

/-- A `k`-expression over the vertex names `Fin n`: a single labelled
vertex, disjoint union, edge addition between two label classes, or
relabelling one class into another. -/
inductive Expr (n k : ℕ) : Type
  /-- The vertex `v`, carrying label `l`. -/
  | leaf (v : Fin n) (l : Fin k)
  /-- Disjoint union `⊕`. -/
  | union (e₁ e₂ : Expr n k)
  /-- `η i j`: join every vertex of class `i` to every vertex of class `j`. -/
  | addEdges (i j : Fin k) (e : Expr n k)
  /-- `ρ i j`: move class `i` into class `j`. -/
  | relabel (i j : Fin k) (e : Expr n k)

/-- The operation performed at a node of a `k`-expression. -/
inductive Op (k : ℕ) where
  /-- Disjoint union. -/
  | union
  /-- Create a vertex with label `l`. -/
  | leaf (l : Fin k)
  /-- `η i j`: join class `i` to class `j`. -/
  | eta (i j : Fin k)
  /-- `ρ i j`: move class `i` into class `j`. -/
  | rho (i j : Fin k)
  deriving DecidableEq

/-- The number naming an operation. The blocks are `union` (one code),
the leaves (`k` codes), the joins and the relabels (`k²` codes each,
the pair `(i, j)` read in base `k`). -/
def Op.code : Op k → ℕ
  | .union => 0
  | .leaf l => 1 + (l : ℕ)
  | .eta i j => 1 + k + ((i : ℕ) * k + (j : ℕ))
  | .rho i j => 1 + k + k * k + ((i : ℕ) * k + (j : ℕ))

end Lax271696.CliqueExpr
end

-- Lax271696.GraphEncoding
section
namespace Lax271696
end Lax271696

namespace Lax271696.GraphEncoding
end Lax271696.GraphEncoding

namespace Lax271696.GraphEncoding.EncodesGraph
end Lax271696.GraphEncoding.EncodesGraph
end

-- Lax271696.InstanceEncoding
section
namespace Lax271696.InstanceEncoding.EncodesExprTree
end Lax271696.InstanceEncoding.EncodesExprTree

namespace Lax271696.InstanceEncoding

open Lax271696.GraphEncoding Lax271696.CliqueExpr

/-- The children of node `i`: the earlier nodes whose parent is `i`,
in increasing order. -/
def children (par : ℕ → ℕ) (i : ℕ) : List ℕ :=
  (List.range i).filter (fun c => par c == i)

/-- The node `i` of the tree given by the three arrays is the
expression `e`: the operation number at `i` is the one of `e`'s
outermost operation, the vertex name at `i` is the one `e` creates if
`e` is a leaf, and the children of `i` — which are listed in increasing
order — are the nodes of `e`'s immediate subexpressions, the left one
first. -/
def EncodesExpr {n k : ℕ} (par lab ids : ℕ → ℕ) : ℕ → Expr n k → Prop
  | i, .leaf v l => children par i = [] ∧ lab i = (Op.leaf l).code ∧ ids i = (v : ℕ)
  | i, .union e₁ e₂ => ∃ c₁ c₂, children par i = [c₁, c₂] ∧
      lab i = (Op.union : Op k).code ∧
      EncodesExpr par lab ids c₁ e₁ ∧ EncodesExpr par lab ids c₂ e₂
  | i, .addEdges a b e => ∃ c, children par i = [c] ∧
      lab i = (Op.eta a b).code ∧ EncodesExpr par lab ids c e
  | i, .relabel a b e => ∃ c, children par i = [c] ∧
      lab i = (Op.rho a b).code ∧ EncodesExpr par lab ids c e

end Lax271696.InstanceEncoding
end
