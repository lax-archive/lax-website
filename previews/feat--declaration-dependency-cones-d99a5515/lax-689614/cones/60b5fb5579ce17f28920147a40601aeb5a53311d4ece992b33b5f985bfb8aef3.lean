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

-- Lax689614.ArcKayles
section
namespace Lax689614
end Lax689614

namespace Lax689614.ArcKayles
end Lax689614.ArcKayles

namespace Lax689614.ArcKayles.Winning
end Lax689614.ArcKayles.Winning
end

-- Lax689614.PositiveCNF
section
namespace Lax689614.PositiveCNF.TrueWins
end Lax689614.PositiveCNF.TrueWins

namespace Lax689614.PositiveCNF

structure Formula where
  nvars : ℕ
  clauses : List (Finset (Fin nvars))

end Lax689614.PositiveCNF
end

-- Lax689614.Encoding
section
namespace Lax689614.Encoding
end Lax689614.Encoding

namespace Lax689614.Encoding.Graph
end Lax689614.Encoding.Graph
end

-- Lax689614.Construction
section
namespace Lax689614.Construction

open PositiveCNF

def K (φ : Formula) : ℕ := 4 * φ.nvars + 6

def R (φ : Formula) : ℕ := φ.clauses.length + 2 * φ.nvars + 2

def v (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + i

def vt (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + R φ + i

def f (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + 2 * R φ + i

def y (φ : Formula) (i : ℕ) : ℕ :=
  2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + i

def z (φ : Formula) (i : ℕ) : ℕ :=
  2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + K φ + i

end Lax689614.Construction
end

-- Lax689614.Grundy
section
namespace Lax689614.Grundy
end Lax689614.Grundy

namespace Lax689614.Grundy.value
end Lax689614.Grundy.value
end

-- Lax689614.RegularPlay
section
namespace Lax689614.RegularPlay.Reachable
end Lax689614.RegularPlay.Reachable

namespace Lax689614.RegularPlay

open PositiveCNF Construction ArcKayles

def SameEdge (u w x z : ℕ) : Prop := (u = x ∧ w = z) ∨ (u = z ∧ w = x)

def RegularMove (φ : Formula) (u w : ℕ) : Prop :=
  (∃ i < R φ, SameEdge u w (v φ i) (vt φ i)) ∨
  (∃ i < φ.nvars, SameEdge u w (v φ i) (f φ i)) ∨
  (∃ i < K φ, SameEdge u w (y φ i) (z φ i))

end Lax689614.RegularPlay
end
