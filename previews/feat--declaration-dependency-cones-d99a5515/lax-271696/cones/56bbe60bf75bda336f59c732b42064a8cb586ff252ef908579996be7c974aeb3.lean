-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax271696.CliqueExpr
section
namespace Lax271696
end Lax271696

namespace Lax271696.CliqueExpr
end Lax271696.CliqueExpr

namespace Lax271696.CliqueExpr.Expr
end Lax271696.CliqueExpr.Expr

namespace Lax271696.CliqueExpr.Op
end Lax271696.CliqueExpr.Op

namespace Lax271696.CliqueExpr.Valid
end Lax271696.CliqueExpr.Valid

namespace Lax271696.CliqueExpr.ValidFor
end Lax271696.CliqueExpr.ValidFor

namespace Lax271696.CliqueExpr.cls
end Lax271696.CliqueExpr.cls

namespace Lax271696.CliqueExpr.leafIds
end Lax271696.CliqueExpr.leafIds

namespace Lax271696.CliqueExpr.Expr.addEdges
end Lax271696.CliqueExpr.Expr.addEdges

namespace Lax271696.CliqueExpr.Expr.leaf
end Lax271696.CliqueExpr.Expr.leaf

namespace Lax271696.CliqueExpr.Expr.relabel
end Lax271696.CliqueExpr.Expr.relabel

namespace Lax271696.CliqueExpr.Expr.union
end Lax271696.CliqueExpr.Expr.union

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
namespace Lax271696.InstanceEncoding.EncodesExpr
end Lax271696.InstanceEncoding.EncodesExpr

namespace Lax271696.InstanceEncoding.EncodesExprTree
end Lax271696.InstanceEncoding.EncodesExprTree

namespace Lax271696.InstanceEncoding

open Lax271696.GraphEncoding Lax271696.CliqueExpr

/-- The number of nodes declared by an expression block: its first
entry. -/
def nodeCount (t : List ℕ) : ℕ := t.getD 0 0

/-- The vertex name created at node `i`, meaningful when the operation
there creates a vertex: the names follow the operations. -/
def vertexName (t : List ℕ) (i : ℕ) : ℕ := t.getD (1 + 2 * nodeCount t + i) 0

end Lax271696.InstanceEncoding
end
