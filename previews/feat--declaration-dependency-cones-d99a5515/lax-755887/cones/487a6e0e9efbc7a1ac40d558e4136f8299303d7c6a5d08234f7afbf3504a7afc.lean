-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.LeaderElection
section
namespace Lax755887.LeaderElection

abbrev State := Fin 3 → Bool

def UniqueLeader (run : State → State) : Prop := ∀ s, ∃! i, run s i = true

structure Protocol where
  run : State → State
  elects : UniqueLeader run

end Lax755887.LeaderElection
end
