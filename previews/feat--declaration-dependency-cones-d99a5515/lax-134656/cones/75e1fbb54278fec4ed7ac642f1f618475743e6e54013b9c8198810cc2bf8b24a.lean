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

-- Lax134656.SuccinctReach
section
namespace Lax134656.SuccinctReach

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive transSysRel : ℕ → Type where
/-- `stateVar x`: the element `x` is a state variable. -/
  | stateVar : transSysRel 1
/-- `next x y`: the element `y` is the next-state copy of the state
  variable `x`. -/
  | next : transSysRel 2
/-- `stepCl c`: the element `c` is a clause of the transition formula. -/
  | stepCl : transSysRel 1
/-- `srcCl c`: the element `c` is a clause of the source formula. -/
  | srcCl : transSysRel 1
/-- `tgtCl c`: the element `c` is a clause of the target formula. -/
  | tgtCl : transSysRel 1
/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : transSysRel 2
/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : transSysRel 2
  deriving DecidableEq

/-- The relational vocabulary of succinctly described transition systems: the
state variables and their next-state copies, three groups of clauses, and the
two literal-occurrence predicates of CNF instances. -/
def transSys : FirstOrder.Language :=
  ⟨fun _ => Empty, transSysRel⟩

/-- `stateVar x`: the element `x` is a state variable. -/
abbrev tsStateVar : transSys.Relations 1 :=
  .stateVar

/-- `next x y`: the element `y` is the next-state copy of the state
  variable `x`. -/
abbrev tsNext : transSys.Relations 2 :=
  .next

open FirstOrder

open Language Structure

section Semantics

variable (A : Type) [transSys.Structure A]

/-- The valuation `ν` *writes* the state `S'`: on the next-state copy of every
state variable it holds exactly the value `S'` gives to that variable. -/
def WritesNext (ν : A → Prop) (S' : A → Prop) : Prop :=
  ∀ x y : A, RelMap tsStateVar ![x] → RelMap tsNext ![x, y] → (ν y ↔ S' x)

end Semantics

end Lax134656.SuccinctReach
end
