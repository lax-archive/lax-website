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

def R (φ : Formula) : ℕ := φ.clauses.length + 2 * φ.nvars + 2

def s : ℕ := 0

def a (_φ : Formula) (j : ℕ) : ℕ := 2 + j

def f (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + 2 * R φ + i

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

def SameEdge (u w x z : ℕ) : Prop := (u = x ∧ w = z) ∨ (u = z ∧ w = x)

def Exhausted (φ : Formula) (S : Finset ℕ) (j : Fin φ.clauses.length) : Prop :=
  ∀ i ∈ φ.clauses[j], f φ i ∉ S

def Exceptional (φ : Formula) (S : Finset ℕ) (u w : ℕ) : Prop :=
  ∃ j : Fin φ.clauses.length, SameEdge u w s (a φ j) ∧ Exhausted φ S j

end Lax783278.RegularPlay
end
