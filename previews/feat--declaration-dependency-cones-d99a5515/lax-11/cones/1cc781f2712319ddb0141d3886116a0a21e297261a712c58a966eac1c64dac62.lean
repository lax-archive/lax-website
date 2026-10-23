-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax11.CliqueExpr
section
namespace Lax11.CliqueExpr.Expr
end Lax11.CliqueExpr.Expr

namespace Lax11.CliqueExpr.Valid
end Lax11.CliqueExpr.Valid

namespace Lax11.CliqueExpr.ValidFor
end Lax11.CliqueExpr.ValidFor

namespace Lax11.CliqueExpr.cls
end Lax11.CliqueExpr.cls

namespace Lax11.CliqueExpr.leafIds
end Lax11.CliqueExpr.leafIds

namespace Lax11.CliqueExpr.Expr.addEdges
end Lax11.CliqueExpr.Expr.addEdges

namespace Lax11.CliqueExpr.Expr.leaf
end Lax11.CliqueExpr.Expr.leaf

namespace Lax11.CliqueExpr.Expr.relabel
end Lax11.CliqueExpr.Expr.relabel

namespace Lax11.CliqueExpr.Expr.union
end Lax11.CliqueExpr.Expr.union

namespace Lax11.CliqueExpr

variable {n k : ℕ}

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

end Lax11.CliqueExpr
end
