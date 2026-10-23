-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

-- Lax783278.ArcKayles
section
namespace Lax783278
end Lax783278

namespace Lax783278.ArcKayles
end Lax783278.ArcKayles

namespace Lax783278.ArcKayles.WinningAfter
end Lax783278.ArcKayles.WinningAfter
end

-- Lax783278.Grundy
section
namespace Lax783278.Grundy
end Lax783278.Grundy

namespace Lax783278.Grundy.valueAfter
end Lax783278.Grundy.valueAfter
end

-- Lax783278.Biclique
section
namespace Lax783278.Biclique.Partition
end Lax783278.Biclique.Partition

namespace Lax783278.Biclique

def g (a b : ℕ) : ℕ := (a + b) % 2 + 2 * (min a b % 2)

end Lax783278.Biclique
end
