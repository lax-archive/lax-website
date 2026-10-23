-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

-- Lax689614.ArcKayles
section
namespace Lax689614.ArcKayles.Winning
end Lax689614.ArcKayles.Winning

namespace Lax689614.ArcKayles

variable {V : Type} [DecidableEq V]

/-- Legal moves, represented by ordered pairs of endpoints. -/
noncomputable def moves (G : SimpleGraph V) (S : Finset V) : Finset (V × V) := by
  classical
  exact (S ×ˢ S).filter fun e => G.Adj e.1 e.2

end Lax689614.ArcKayles
end
