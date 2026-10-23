-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.FortifiedSquaring
section
namespace Lax253009.FortifiedSquaring
end Lax253009.FortifiedSquaring

namespace Lax253009.FortifiedSquaring.Game
end Lax253009.FortifiedSquaring.Game
end

-- Lax253009.TupleFortification
section
namespace Lax253009.TupleFortification

open FortifiedSquaring

open scoped BigOperators

abbrev History (t : ℕ) (W : Type) := Fin t × (Fin t → W)

end Lax253009.TupleFortification
end
