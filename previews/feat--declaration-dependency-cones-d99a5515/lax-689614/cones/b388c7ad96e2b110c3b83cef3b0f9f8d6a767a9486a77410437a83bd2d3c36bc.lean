-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

-- Lax689614.ArcKayles
section
namespace Lax689614
end Lax689614

namespace Lax689614.ArcKayles
end Lax689614.ArcKayles

namespace Lax689614.ArcKayles.Winning
end Lax689614.ArcKayles.Winning
end

-- Lax689614.Grundy
section
namespace Lax689614.Grundy
end Lax689614.Grundy

namespace Lax689614.Grundy.value
end Lax689614.Grundy.value
end

-- Lax689614.Biclique
section
namespace Lax689614.Biclique.Partition
end Lax689614.Biclique.Partition

namespace Lax689614.Biclique

def g (a b : ℕ) : ℕ := (a + b) % 2 + 2 * (min a b % 2)

end Lax689614.Biclique
end
