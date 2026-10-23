-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax271696.CliqueExpr
section
namespace Lax271696.CliqueExpr.Op
end Lax271696.CliqueExpr.Op

namespace Lax271696.CliqueExpr.Valid
end Lax271696.CliqueExpr.Valid

namespace Lax271696.CliqueExpr.ValidFor
end Lax271696.CliqueExpr.ValidFor

namespace Lax271696.CliqueExpr.cls
end Lax271696.CliqueExpr.cls

namespace Lax271696.CliqueExpr.Op.code
end Lax271696.CliqueExpr.Op.code

namespace Lax271696.CliqueExpr.Op.eta
end Lax271696.CliqueExpr.Op.eta

namespace Lax271696.CliqueExpr.Op.leaf
end Lax271696.CliqueExpr.Op.leaf

namespace Lax271696.CliqueExpr.Op.rho
end Lax271696.CliqueExpr.Op.rho

namespace Lax271696.CliqueExpr.Op.union
end Lax271696.CliqueExpr.Op.union

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

/-- The vertex names created by the leaves, in order. -/
def leafIds : Expr n k → List (Fin n)
  | .leaf v _ => [v]
  | .union e₁ e₂ => leafIds e₁ ++ leafIds e₂
  | .addEdges _ _ e => leafIds e
  | .relabel _ _ e => leafIds e

/-- The vertex set of an expression. -/
def verts : Expr n k → Finset (Fin n)
  | .leaf v _ => {v}
  | .union e₁ e₂ => verts e₁ ∪ verts e₂
  | .addEdges _ _ e => verts e
  | .relabel _ _ e => verts e

end Lax271696.CliqueExpr
end
