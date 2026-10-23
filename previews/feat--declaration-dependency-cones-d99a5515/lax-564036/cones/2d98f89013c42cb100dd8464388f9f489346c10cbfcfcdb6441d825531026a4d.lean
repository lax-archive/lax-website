-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
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

-- Lax564036.QuantifiedBooleanFormulas
section
namespace Lax564036.QuantifiedBooleanFormulas.QbfMatrix
end Lax564036.QuantifiedBooleanFormulas.QbfMatrix

namespace Lax564036.QuantifiedBooleanFormulas.altQuant
end Lax564036.QuantifiedBooleanFormulas.altQuant

namespace Lax564036.QuantifiedBooleanFormulas

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of quantified Boolean formulas with `k`
quantifier blocks. -/
inductive qbfRel (k : ℕ) : ℕ → Type
  /-- `isClause c`: the element `c` is a clause (a term, for a disjunctive
  matrix). -/
  | isClause : qbfRel k 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : qbfRel k 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : qbfRel k 2
  /-- `block i x`: the variable `x` belongs to the `i`-th quantifier block. -/
  | block : Fin k → qbfRel k 1
  deriving DecidableEq

/-- The relational vocabulary of quantified Boolean formulas with `k`
quantifier blocks: that of CNF instances, together with `k` unary predicates
marking the variables of each quantifier block. -/
def qbf (k : ℕ) : Language :=
  ⟨fun _ => Empty, qbfRel k⟩

variable {k : ℕ}

/-- The symbol for “is a clause”. -/
abbrev qbfIsClause : (qbf k).Relations 1 := .isClause

open FirstOrder

open Language Structure

section Matrix

variable {k : ℕ} {A : Type} [(qbf k).Structure A]

end Matrix

end Lax564036.QuantifiedBooleanFormulas
end
