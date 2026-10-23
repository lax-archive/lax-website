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

-- Lax117284.BoundedSat
section
namespace Lax117284.BoundedSat

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/-- A **[2,3]-bounded 3-SAT formula** over `vars` variables: `twoClauses` clauses of two
literals and `threeClauses` clauses of three literals, in which every literal — a variable
together with a sign — occupies at most two of the positions of the formula. -/
structure Formula where
  /-- The number of variables. -/
  vars : ℕ
  /-- The number of clauses of two literals. -/
  twoClauses : ℕ
  /-- The number of clauses of three literals. -/
  threeClauses : ℕ
  /-- The literals of the clauses of two literals. -/
  aLit : Fin twoClauses → Fin 2 → Fin vars × Bool
  /-- The literals of the clauses of three literals. -/
  bLit : Fin threeClauses → Fin 3 → Fin vars × Bool
  /-- Every literal occurs at most twice in the formula. -/
  occ_le_two : ∀ l : Fin vars × Bool,
    (Finset.univ.filter fun o : (Fin twoClauses × Fin 2) ⊕ (Fin threeClauses × Fin 3) =>
      Sum.elim (fun q => aLit q.1 q.2) (fun q => bLit q.1 q.2) o = l).card ≤ 2

namespace Formula

variable (φ : Formula)

end Formula

/-- The literal occupying the occurrence slot `o`, read off unnumbered indices: the two
slots of every clause of two literals come first, then the three slots of every clause of
three literals. Outside the formula the value is the positive literal of the variable `0`.
It is in this form that a construction reads a formula. -/
def litOfSlot (φ : Formula) (o : ℕ) : ℕ × Bool :=
  if o < 2 * φ.twoClauses then
    if hj : o / 2 < φ.twoClauses then
      ((φ.aLit ⟨o / 2, hj⟩ ⟨o % 2, by omega⟩).1, (φ.aLit ⟨o / 2, hj⟩ ⟨o % 2, by omega⟩).2)
    else (0, true)
  else
    if hj : (o - 2 * φ.twoClauses) / 3 < φ.threeClauses then
      ((φ.bLit ⟨(o - 2 * φ.twoClauses) / 3, hj⟩ ⟨(o - 2 * φ.twoClauses) % 3, by omega⟩).1,
        (φ.bLit ⟨(o - 2 * φ.twoClauses) / 3, hj⟩ ⟨(o - 2 * φ.twoClauses) % 3, by omega⟩).2)
    else (0, true)

/-- Which of the occurrences of its own literal the slot `o` is: the number of earlier
slots carrying the same literal. Under the occurrence bound this is `0` or `1`. -/
def slotRank (φ : Formula) (o : ℕ) : ℕ :=
  (List.range o).countP fun o' => litOfSlot φ o' == litOfSlot φ o

end Lax117284.BoundedSat
end
