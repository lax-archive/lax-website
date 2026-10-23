-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

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
namespace Lax783278.Encoding.Graph
end Lax783278.Encoding.Graph

namespace Lax783278.Encoding

open scoped Classical

open Lax434930.PolynomialTime

def formulaWord (φ : PositiveCNF.Formula) : Word :=
  List.replicate φ.nvars true ++ [false] ++
    List.replicate φ.clauses.length true ++ [false] ++
    φ.clauses.flatMap fun C =>
      (List.finRange φ.nvars).map fun x => decide (x ∈ C)

end Lax783278.Encoding
end
