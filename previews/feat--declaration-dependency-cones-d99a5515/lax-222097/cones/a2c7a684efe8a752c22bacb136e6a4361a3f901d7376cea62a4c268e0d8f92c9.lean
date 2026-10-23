-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax222097.GraphEncoding
section
namespace Lax222097
end Lax222097

namespace Lax222097.GraphEncoding
end Lax222097.GraphEncoding

namespace Lax222097.GraphEncoding.Instance
end Lax222097.GraphEncoding.Instance
end

-- Lax222097.MaxCut
section
namespace Lax222097.MaxCut

open scoped Classical

open Finset

/-- All edges, each listed once with its smaller endpoint first. -/
noncomputable def edges {n : ℕ} (F : SimpleGraph (Fin n)) :
    Finset (Fin n × Fin n) :=
  univ.filter fun e => e.1 < e.2 ∧ F.Adj e.1 e.2

/-- The number of edges crossing between `S` and its complement. -/
noncomputable def cutSize {n : ℕ} (F : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  ((edges F).filter fun e =>
    (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)).card

/-- The largest cut size over all subsets of vertices. -/
noncomputable def maxCut {n : ℕ} (F : SimpleGraph (Fin n)) : ℕ :=
  (univ : Finset (Fin n)).powerset.sup (cutSize F)

end Lax222097.MaxCut
end
