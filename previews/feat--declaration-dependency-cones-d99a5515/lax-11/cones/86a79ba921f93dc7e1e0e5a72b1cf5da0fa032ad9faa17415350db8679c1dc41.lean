-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax11.CliqueExpr
section
namespace Lax11.CliqueExpr.Expr
end Lax11.CliqueExpr.Expr

namespace Lax11.CliqueExpr.Op
end Lax11.CliqueExpr.Op

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

/-- The size of the operation alphabet. -/
def opCard (k : ℕ) : ℕ := 1 + k + 2 * (k * k)

end Lax11.CliqueExpr
end
