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

def s : ℕ := 0

def t : ℕ := 1

def a (_φ : Formula) (j : ℕ) : ℕ := 2 + j

def b (φ : Formula) (j : ℕ) : ℕ := 2 + φ.clauses.length + j

def v (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + i

def vt (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + R φ + i

def f (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + 2 * R φ + i

def y (φ : Formula) (i : ℕ) : ℕ :=
  2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + i

def z (φ : Formula) (i : ℕ) : ℕ :=
  2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + K φ + i

def Edge (φ : Formula) (u w : ℕ) : Prop :=
  (u = s ∧ w = t) ∨
  (∃ j < φ.clauses.length, u = s ∧ w = a φ j) ∨
  (∃ j < φ.clauses.length, u = a φ j ∧ w = b φ j) ∨
  (∃ j < φ.clauses.length, ∃ i < R φ, u = b φ j ∧ w = v φ i) ∨
  (∃ i < R φ, u = v φ i ∧ w = vt φ i) ∨
  (∃ i < φ.nvars, u = v φ i ∧ w = f φ i) ∨
  (∃ j : Fin φ.clauses.length, ∃ i ∈ φ.clauses[j],
    u = b φ j ∧ w = f φ i) ∨
  (∃ i < K φ, u = s ∧ w = y φ i) ∨
  (∃ i < K φ, u = y φ i ∧ w = z φ i)

def graph (φ : Formula) : SimpleGraph ℕ := SimpleGraph.fromRel (Edge φ)

end Lax689614.Construction
end
