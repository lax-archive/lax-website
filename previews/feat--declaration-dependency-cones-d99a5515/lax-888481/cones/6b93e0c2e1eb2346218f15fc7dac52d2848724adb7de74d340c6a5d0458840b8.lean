-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold

-- Lax888481.Scheduling
section
namespace Lax888481
end Lax888481

namespace Lax888481.Scheduling
end Lax888481.Scheduling

namespace Lax888481.Scheduling.Instance
end Lax888481.Scheduling.Instance
end

-- Lax888481.InstanceEncoding
section
namespace Lax888481.InstanceEncoding.EncodesInstance
end Lax888481.InstanceEncoding.EncodesInstance

namespace Lax888481.InstanceEncoding

open Lax888481.Scheduling

/-- The number of machines declared by a word: its second entry. -/
def machineCount (x : List ℕ) : ℕ := x.getD 1 0

end Lax888481.InstanceEncoding
end
