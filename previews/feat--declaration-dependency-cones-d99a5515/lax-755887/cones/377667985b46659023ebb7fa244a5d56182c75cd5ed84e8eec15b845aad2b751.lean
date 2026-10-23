-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.LeaderElection
section
namespace Lax755887.LeaderElection.Protocol
end Lax755887.LeaderElection.Protocol

namespace Lax755887.LeaderElection

abbrev State := Fin 3 → Bool

def next (i : Fin 3) : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

def rotate (s : State) : State := fun i => s (next i)

def Equivariant (run : State → State) : Prop := ∀ s, run (rotate s) = rotate (run s)

end Lax755887.LeaderElection
end

-- Lax755887.LeaderControls
section
namespace Lax755887.LeaderControls

open Lax755887.LeaderElection

axiom equivariance_has_model : ∃ run, Equivariant run

end Lax755887.LeaderControls
end
