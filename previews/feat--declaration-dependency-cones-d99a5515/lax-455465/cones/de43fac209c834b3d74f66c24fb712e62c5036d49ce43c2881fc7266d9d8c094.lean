-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.NNReal.Basic

-- Lax455465.ProductNetwork
section
namespace Lax455465.ProductNetwork.Network
end Lax455465.ProductNetwork.Network

open scoped BigOperators NNReal

namespace Lax455465.ProductNetwork

/-- Whether capacities are shared by both directions of an edge or belong
to individual directed arcs. -/
inductive EdgeKind
  /-- One capacity shared by both directions of an undirected edge. -/
  | undirected
  /-- A separate capacity for each directed arc. -/
  | directed
  deriving DecidableEq

end Lax455465.ProductNetwork
end
