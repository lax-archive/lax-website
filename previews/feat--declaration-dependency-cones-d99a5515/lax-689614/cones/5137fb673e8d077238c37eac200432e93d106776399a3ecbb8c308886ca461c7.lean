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

def b (φ : Formula) (j : ℕ) : ℕ := 2 + φ.clauses.length + j

end Lax689614.Construction
end
