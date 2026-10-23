-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax11.CliqueExpr
section
namespace Lax11.CliqueExpr.Op
end Lax11.CliqueExpr.Op

namespace Lax11.CliqueExpr.ValidFor
end Lax11.CliqueExpr.ValidFor

namespace Lax11.CliqueExpr.cls
end Lax11.CliqueExpr.cls

namespace Lax11.CliqueExpr.Op.code
end Lax11.CliqueExpr.Op.code

namespace Lax11.CliqueExpr.Op.eta
end Lax11.CliqueExpr.Op.eta

namespace Lax11.CliqueExpr.Op.leaf
end Lax11.CliqueExpr.Op.leaf

namespace Lax11.CliqueExpr.Op.rho
end Lax11.CliqueExpr.Op.rho

namespace Lax11.CliqueExpr.Op.union
end Lax11.CliqueExpr.Op.union

namespace Lax11.CliqueExpr

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

/-- Well-formedness of the operations: `addEdges` joins two *different*
classes, the standard restriction on `η`. -/
def opsOk : Expr n k → Bool
  | .leaf _ _ => true
  | .union e₁ e₂ => opsOk e₁ && opsOk e₂
  | .addEdges i j e => (i != j) && opsOk e
  | .relabel _ _ e => opsOk e

/-- A valid expression: the leaves create pairwise distinct vertices —
which is what makes the two sides of every `⊕` disjoint — and the
operations are well formed. -/
structure Valid (e : Expr n k) : Prop where
  /-- No vertex name is created twice. -/
  nodup : (leafIds e).Nodup
  /-- Every `addEdges` joins two different classes. -/
  ops : opsOk e = true

end Lax11.CliqueExpr
end
