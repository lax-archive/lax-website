-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Semantics

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax485149.Complement
section
namespace Lax485149
end Lax485149

namespace Lax485149.Complement
end Lax485149.Complement

namespace Lax485149.Complement.DecisionProblem
end Lax485149.Complement.DecisionProblem
end

-- Lax485149.Problems
section
namespace Lax485149
end Lax485149

namespace Lax485149.Problems
end Lax485149.Problems

namespace Lax485149.Problems.DecisionProblem
end Lax485149.Problems.DecisionProblem

namespace Lax485149.Problems.DecisionProblem.ofPred
end Lax485149.Problems.DecisionProblem.ofPred
end

-- Lax485149.Reachability
section
namespace Lax485149.Reachability

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open Lax904597.Problems Lax485149.Problems Lax485149.Complement

/-- The relation symbols of graphs with marked sources and targets. -/
inductive stGraphRel : ℕ → Type where
  /-- `edge a b`: there is an edge from `a` to `b`. -/
  | edge : stGraphRel 2
  /-- `source a`: the vertex `a` is a marked source. -/
  | source : stGraphRel 1
  /-- `target a`: the vertex `a` is a marked target. -/
  | target : stGraphRel 1
  deriving DecidableEq

/-- The relational vocabulary of directed graphs with marked sources and
targets. -/
def stGraph : Language :=
  ⟨fun _ => Empty, stGraphRel⟩

end Lax485149.Reachability
end
