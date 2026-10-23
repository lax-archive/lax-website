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
namespace Lax783278.Grundy.valueAfter
end Lax783278.Grundy.valueAfter

namespace Lax783278.Grundy

open ArcKayles

/-- The least natural number not in the finite set `S`. -/
noncomputable def mex (S : Finset ℕ) : ℕ := sInf {n : ℕ | n ∉ S}

end Lax783278.Grundy
end
