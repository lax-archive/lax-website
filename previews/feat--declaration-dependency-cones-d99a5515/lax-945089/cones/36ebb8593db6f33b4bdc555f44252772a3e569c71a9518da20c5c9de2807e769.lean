-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Group.Even
import Mathlib.Data.Set.Card
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

-- Lax945089.Parity
section
namespace Lax945089.Parity

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive markedSetRel : ℕ → Type where
/-- `mark x`: the element `x` belongs to the marked subset. -/
  | mark : markedSetRel 1
  deriving DecidableEq

/-- The relational vocabulary of a *marked subset*: a finite set with a
distinguished subset of it. -/
def markedSet : FirstOrder.Language :=
  ⟨fun _ => Empty, markedSetRel⟩

open FirstOrder

open Language Structure

section Problem

variable (A : Type) [markedSet.Structure A]

end Problem

end Lax945089.Parity
end
