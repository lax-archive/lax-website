-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Real.Basic

-- Lax391470.Scheduling
section
namespace Lax391470
end Lax391470

namespace Lax391470.Scheduling
end Lax391470.Scheduling

namespace Lax391470.Scheduling.Instance
end Lax391470.Scheduling.Instance
end

-- Lax391470.AuxiliaryProblem
section
namespace Lax391470.AuxiliaryProblem
end Lax391470.AuxiliaryProblem

namespace Lax391470.AuxiliaryProblem.Instance
end Lax391470.AuxiliaryProblem.Instance

namespace Lax391470.AuxiliaryProblem.Instance.Ordered
end Lax391470.AuxiliaryProblem.Instance.Ordered
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax429075.CNF
section
namespace Lax429075.CNF

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

abbrev Clause := List Literal

abbrev Formula := List Clause

end Lax429075.CNF
end

-- Lax391470.SatConstruction
section
namespace Lax391470.SatConstruction.ordRelease
end Lax391470.SatConstruction.ordRelease

namespace Lax391470.SatConstruction

open Lax391470.AuxiliaryProblem Lax429075.CNF

variable (p q : ℕ) (F : Formula)

/-- The number `m` of clauses. -/
def numClauses : ℕ := F.length

/-- The length `S` of a section. -/
def sectionLength : ℕ := p + 2 * q + numClauses F * (p + q) + 1 + q

/-- The start of section `s`. -/
def sectionStart (s : ℕ) : ℕ := sectionLength p q F * s

/-- The start of the clause block of clause `j` in section `s`. -/
def clauseStart (s j : ℕ) : ℕ := sectionStart p q F s + p + 2 * q + j * (p + q)

/-- The late deadline of both pending jobs of a clause block. -/
def clauseDue (s j : ℕ) : ℕ := clauseStart p q F s j + p + q + 1

/-- The variable whose group the pair `i` belongs to. -/
def groupOf (i : ℕ) : ℕ := i / (1 + 2 * numClauses F)

/-- The position of the pair `i` in its group: `0` for the literal pair. -/
def posOf (i : ℕ) : ℕ := i % (1 + 2 * numClauses F)

/-- The section holding the long job of the clause pair `i`. -/
def pairSection (i : ℕ) : ℕ := 2 * groupOf F i + (posOf F i - 1) / numClauses F

/-- The clause of the clause pair `i`. -/
def pairClause (i : ℕ) : ℕ := (posOf F i - 1) % numClauses F

/-- The late deadline of the short job of pair `i`. -/
def shortDue (i : ℕ) : ℕ :=
  if posOf F i = 0 then sectionStart p q F (2 * groupOf F i + 1) + p + 2 * q
  else clauseDue p q F (pairSection F i + 1) (pairClause F i)

end Lax391470.SatConstruction
end
