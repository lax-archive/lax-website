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

-- Lax11.GraphEncoding
section
namespace Lax11
end Lax11

namespace Lax11.GraphEncoding
end Lax11.GraphEncoding

namespace Lax11.GraphEncoding.EncodesGraph
end Lax11.GraphEncoding.EncodesGraph
end

-- Lax11.InstanceEncoding
section
namespace Lax11.InstanceEncoding.EncodesExpr
end Lax11.InstanceEncoding.EncodesExpr

namespace Lax11.InstanceEncoding

open Lax11.GraphEncoding Lax11.CliqueExpr

/-- The number of nodes declared by an expression block: its first
entry. -/
def nodeCount (t : List ℕ) : ℕ := t.getD 0 0

/-- The parent of node `i`: the parents follow the header entry. -/
def parent (t : List ℕ) (i : ℕ) : ℕ := t.getD (1 + i) 0

/-- The operation performed at node `i`, as a number: the operations
follow the parents. -/
def opCode (t : List ℕ) (i : ℕ) : ℕ := t.getD (1 + nodeCount t + i) 0

/-- The word `t` is an expression block for a tree whose operations are
operations of `k`-expressions. The number of nodes is the block's own
first entry, so it is read off `t` rather than quantified over. -/
structure EncodesExprTree (t : List ℕ) (k : ℕ) : Prop where
  /-- There is at least one node: an expression has a root. -/
  pos : 1 ≤ nodeCount t
  /-- The block consists of the header entry and three arrays of one
  number per node. -/
  length_eq : t.length = 1 + 3 * nodeCount t
  /-- Every node but the last has a parent, which is a later node — so
  children are numbered before their parents and the root is the last
  node. -/
  parent_gt : ∀ i, i + 1 < nodeCount t → i < parent t i ∧ parent t i < nodeCount t
  /-- Every operation entry is the number of an operation. -/
  opCode_lt : ∀ i < nodeCount t, opCode t i < opCard k

end Lax11.InstanceEncoding
end
