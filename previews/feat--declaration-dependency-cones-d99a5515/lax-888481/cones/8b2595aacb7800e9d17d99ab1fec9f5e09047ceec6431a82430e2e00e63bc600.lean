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

/-- The number of jobs declared by a word: its first entry. -/
def jobCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The `t`-th entry of the target array, which follows the offsets. -/
def target (x : List ℕ) (t : ℕ) : ℕ := x.getD (3 + 4 * jobCount x + t) 0

end Lax888481.InstanceEncoding
end
