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

/-- `tgtCl c`: the element `c` is a clause of the target formula. -/
abbrev tsTgtCl : transSys.Relations 1 :=
  .tgtCl

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev tsPosIn : transSys.Relations 2 :=
  .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev tsNegIn : transSys.Relations 2 :=
  .negIn

open FirstOrder

open Language Structure

section Semantics

variable (A : Type) [transSys.Structure A]

/-- A valuation satisfies a group of clauses when every clause of the group
contains a literal it makes true. Elements that are not clauses of the group
impose nothing, exactly as for satisfiability. -/
def ClausesHold (ν : A → Prop) (grp : transSys.Relations 1) : Prop :=
  ∀ c : A, RelMap grp ![c] →
    ∃ x : A, (RelMap tsPosIn ![c, x] ∧ ν x) ∨ (RelMap tsNegIn ![c, x] ∧ ¬ν x)

/-- The valuation `ν` *reads* the state `S`: on every state variable it agrees
with `S`. This is the only way a clause group sees the current state. -/
def ReadsCur (ν : A → Prop) (S : A → Prop) : Prop :=
  ∀ x : A, RelMap tsStateVar ![x] → (ν x ↔ S x)

/-- A state is a target state when some valuation reading it satisfies every
clause of the target formula. -/
def IsGoal (S : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsTgtCl ∧ ReadsCur A ν S

end Semantics

end Lax134656.SuccinctReach
end
