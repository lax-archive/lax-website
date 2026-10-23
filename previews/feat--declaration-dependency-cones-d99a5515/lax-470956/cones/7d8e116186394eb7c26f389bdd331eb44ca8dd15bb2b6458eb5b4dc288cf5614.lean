-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold

-- Lax470956.Scheduling
section
namespace Lax470956
end Lax470956

namespace Lax470956.Scheduling
end Lax470956.Scheduling

namespace Lax470956.Scheduling.Instance
end Lax470956.Scheduling.Instance
end

-- Lax470956.InstanceEncoding
section
namespace Lax470956.InstanceEncoding.EncodesInstance
end Lax470956.InstanceEncoding.EncodesInstance

namespace Lax470956.InstanceEncoding

open Lax470956.Scheduling

/-- The number of jobs declared by a word: its first entry. -/
def jobCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The `t`-th entry of the target array, which follows the offsets. -/
def target (x : List ℕ) (t : ℕ) : ℕ := x.getD (3 + 4 * jobCount x + t) 0

end Lax470956.InstanceEncoding
end
