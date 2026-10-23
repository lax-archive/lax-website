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

-- Lax564036.SatUnsat
section
namespace Lax564036.SatUnsat

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of *pairs* of CNF instances: two copies of
the symbols of CNF instances, one per side. -/
inductive satPairRel : ℕ → Type
  /-- `isClause₁ c`: `c` is a clause of the first formula. -/
  | isClause₁ : satPairRel 1
  /-- `posIn₁ c x`: `x` occurs positively in the first formula's clause `c`. -/
  | posIn₁ : satPairRel 2
  /-- `negIn₁ c x`: `x` occurs negatively in the first formula's clause `c`. -/
  | negIn₁ : satPairRel 2
  /-- `isClause₂ c`: `c` is a clause of the second formula. -/
  | isClause₂ : satPairRel 1
  /-- `posIn₂ c x`: `x` occurs positively in the second formula's clause `c`. -/
  | posIn₂ : satPairRel 2
  /-- `negIn₂ c x`: `x` occurs negatively in the second formula's clause `c`. -/
  | negIn₂ : satPairRel 2
  deriving DecidableEq

/-- The relational vocabulary of pairs of CNF instances. -/
def satPair : Language :=
  ⟨fun _ => Empty, satPairRel⟩

/-- “Occurs positively in”, first formula. -/
abbrev spPos₁ : satPair.Relations 2 := .posIn₁

open FirstOrder

open Language Structure

section Defs

variable (A : Type) [satPair.Structure A]

end Defs

end Lax564036.SatUnsat
end
