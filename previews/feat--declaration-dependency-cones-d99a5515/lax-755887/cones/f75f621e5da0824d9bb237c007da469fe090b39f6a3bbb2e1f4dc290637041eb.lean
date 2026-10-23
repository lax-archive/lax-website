-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.Stuttering
section
namespace Lax755887.Stuttering

abbrev State := ℕ × Bool

def tick (s : State) : State := if s.2 then (s.1 - 1, false) else (s.1, true)

def Step (next current : State) : Prop := next = tick current

end Lax755887.Stuttering
end
