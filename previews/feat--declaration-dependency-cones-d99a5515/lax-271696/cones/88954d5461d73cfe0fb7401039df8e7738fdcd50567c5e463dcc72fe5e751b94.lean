-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax271696.CliqueExpr
section
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

namespace Lax271696.CliqueExpr

variable {n k : ℕ}

/-- The size of the operation alphabet. -/
def opCard (k : ℕ) : ℕ := 1 + k + 2 * (k * k)

end Lax271696.CliqueExpr
end
