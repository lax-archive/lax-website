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
namespace Lax783278
end Lax783278

namespace Lax783278.PositiveCNF
end Lax783278.PositiveCNF

namespace Lax783278.PositiveCNF.Formula
end Lax783278.PositiveCNF.Formula

namespace Lax783278.PositiveCNF.TrueWinsAfter
end Lax783278.PositiveCNF.TrueWinsAfter
end

-- Lax783278.Encoding
section
namespace Lax783278.Encoding

open scoped Classical

open Lax434930.PolynomialTime

structure Graph where
  vertices : ℕ
  graph : SimpleGraph (Fin vertices)

end Lax783278.Encoding
end
