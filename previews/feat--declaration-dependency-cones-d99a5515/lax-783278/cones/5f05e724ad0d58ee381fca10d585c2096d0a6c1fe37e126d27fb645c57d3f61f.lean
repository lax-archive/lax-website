-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax783278.ArcKayles
section
namespace Lax783278
end Lax783278

namespace Lax783278.ArcKayles
end Lax783278.ArcKayles

namespace Lax783278.ArcKayles.WinningAfter
end Lax783278.ArcKayles.WinningAfter
end

-- Lax783278.PositiveCNF
section
namespace Lax783278.PositiveCNF.TrueWinsAfter
end Lax783278.PositiveCNF.TrueWinsAfter

namespace Lax783278.PositiveCNF

/-- A conjunction of clauses, each a disjunction of positive variables. -/
structure Formula where
  /-- Number of variables, labeled from zero. -/
  nvars : ℕ
  /-- The clauses; an empty clause makes the formula unsatisfiable. -/
  clauses : List (Finset (Fin nvars))

end Lax783278.PositiveCNF
end

-- Lax783278.Encoding
section
namespace Lax783278.Encoding
end Lax783278.Encoding

namespace Lax783278.Encoding.Graph
end Lax783278.Encoding.Graph
end

-- Lax783278.Construction
section
namespace Lax783278.Construction

open PositiveCNF

def K (φ : Formula) : ℕ := 4 * φ.nvars + 6

def R (φ : Formula) : ℕ := φ.clauses.length + 2 * φ.nvars + 2

def y (φ : Formula) (i : ℕ) : ℕ :=
  2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + i

end Lax783278.Construction
end

-- Lax783278.Grundy
section
namespace Lax783278.Grundy
end Lax783278.Grundy

namespace Lax783278.Grundy.valueAfter
end Lax783278.Grundy.valueAfter
end

-- Lax783278.RegularPlay
section
namespace Lax783278.RegularPlay.Reachable
end Lax783278.RegularPlay.Reachable

namespace Lax783278.RegularPlay

open PositiveCNF Construction ArcKayles

def remainingY (φ : Formula) (S : Finset ℕ) : ℕ :=
  ((Finset.range (K φ)).filter fun i => y φ i ∈ S).card

end Lax783278.RegularPlay
end
