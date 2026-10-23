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

-- Lax762056.GraphEncoding
section
namespace Lax762056
end Lax762056

namespace Lax762056.GraphEncoding
end Lax762056.GraphEncoding

namespace Lax762056.GraphEncoding.Instance
end Lax762056.GraphEncoding.Instance
end

-- Lax762056.MaxCut
section
namespace Lax762056.MaxCut

open Finset

noncomputable def edges {n : ℕ} (F : SimpleGraph (Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  exact univ.filter fun e => e.1 < e.2 ∧ F.Adj e.1 e.2

noncomputable def cutSize {n : ℕ} (F : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ := by
  classical
  exact ((edges F).filter fun e =>
    (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)).card

noncomputable def maxCut {n : ℕ} (F : SimpleGraph (Fin n)) : ℕ :=
  (univ : Finset (Fin n)).powerset.sup (cutSize F)

end Lax762056.MaxCut
end
