-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

-- Lax535992.Game
section
namespace Lax535992.Game.WinsOn
end Lax535992.Game.WinsOn

namespace Lax535992.Game

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive andOrGraphRel : ℕ → Type where
/-- `move a b`: the player to move at `a` may move to `b`. -/
  | move : andOrGraphRel 2
/-- `univ a`: the node `a` belongs to the universal player. -/
  | univ : andOrGraphRel 1
/-- `start a`: the node `a` is a marked starting position. -/
  | start : andOrGraphRel 1
/-- `won a`: the node `a` wins outright. -/
  | won : andOrGraphRel 1
  deriving DecidableEq

/-- The relational vocabulary of AND/OR graphs: a move relation, a mark for the
nodes of the universal player, a mark for the starting positions and a mark for
the positions that win outright. -/
def andOrGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, andOrGraphRel⟩

/-- `start a`: the node `a` is a marked starting position. -/
abbrev agStart : andOrGraph.Relations 1 :=
  .start

open FirstOrder

open Language Structure

section Defs

variable {A : Type} [andOrGraph.Structure A]

/-- `start a`: the node `a` is a marked starting position.  -/
def AGStart {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agStart ![a0]

end Defs

end Lax535992.Game
end
