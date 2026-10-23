-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Order.Interval.Set.Basic

-- Lax117284.Scheduling
section
namespace Lax117284
end Lax117284

namespace Lax117284.Scheduling
end Lax117284.Scheduling

namespace Lax117284.Scheduling.Instance
end Lax117284.Scheduling.Instance
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
end

-- Lax117284.Problems
section
namespace Lax117284.Problems
end Lax117284.Problems
end

-- Lax117284.TwoSatisfiability
section
namespace Lax117284.TwoSatisfiability

open Lax434930.PolynomialTime

/-- A **2-CNF formula**: `clauses` clauses over `vars` variables, each clause a pair of
literals, a literal being a variable together with a sign. -/
structure Formula where
  /-- The number of variables. -/
  vars : ℕ
  /-- The number of clauses. -/
  clauses : ℕ
  /-- The two literals of each clause. -/
  lit : Fin clauses → Fin 2 → Fin vars × Bool

namespace Formula

variable (φ : Formula)

/-- An assignment of a truth value to every variable. -/
abbrev Assignment := Fin φ.vars → Bool

/-- The assignment `a` satisfies `φ`: every clause has a literal that holds. -/
def Satisfies (a : φ.Assignment) : Prop :=
  ∀ c, ∃ α, a (φ.lit c α).1 = (φ.lit c α).2

/-- **The question of 2-satisfiability**: is there a satisfying assignment? -/
def Satisfiable : Prop := ∃ a : φ.Assignment, φ.Satisfies a

end Formula

end Lax117284.TwoSatisfiability
end
