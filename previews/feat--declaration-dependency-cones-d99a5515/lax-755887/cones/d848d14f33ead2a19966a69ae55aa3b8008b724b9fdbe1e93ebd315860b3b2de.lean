-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.LeaderElection
section
namespace Lax755887.LeaderElection.Protocol
end Lax755887.LeaderElection.Protocol

namespace Lax755887.LeaderElection

def next (i : Fin 3) : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

end Lax755887.LeaderElection
end
