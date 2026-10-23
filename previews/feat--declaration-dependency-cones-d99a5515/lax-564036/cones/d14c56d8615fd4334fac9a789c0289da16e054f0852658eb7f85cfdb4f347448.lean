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

-- Lax904597.Sat
section
namespace Lax904597.Sat

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

/-- The relation symbols of CNF instances. -/
inductive satRel : ℕ → Type where
  /-- `isClause c`: the element `c` is a clause. -/
  | isClause : satRel 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : satRel 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : satRel 2
  deriving DecidableEq

/-- The relational language of CNF instances: a unary predicate singling out
clauses, and two binary predicates for positive and negative occurrences of a
variable in a clause. -/
def sat : Language :=
  ⟨fun _ => Empty, satRel⟩

/-- `isClause c`: the element `c` is a clause. -/
abbrev satIsClause : sat.Relations 1 := .isClause

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev satPosIn : sat.Relations 2 := .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev satNegIn : sat.Relations 2 := .negIn

end Lax904597.Sat
end

-- Lax564036.Tautology
section
namespace Lax564036.Tautology

open Lax904597.Problems Lax485149.Problems

open Lax904597.Sat

open FirstOrder

open Language Structure BoundedFormula

section Taut

variable (A : Type) [sat.Structure A]

/-- A CNF instance of the NP core, read as a formula in disjunctive normal form,
is a *tautology* when every assignment of truth values to its elements makes
some term true – that is, satisfies every literal of that term. (Elements that
are not variables of the formula may be assigned arbitrarily; they are harmless
since no term mentions them.) -/
def Tautology : Prop :=
  ∀ ν : A → Prop, ∃ c : A, RelMap satIsClause ![c] ∧
    ∀ x : A, (RelMap satPosIn ![c, x] → ν x) ∧ (RelMap satNegIn ![c, x] → ¬ν x)

end Taut

end Lax564036.Tautology
end
