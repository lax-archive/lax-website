-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.ReusedKey
section
namespace Lax755887.ReusedKey

def transcript (secret key : Bool) : Bool × Bool := (key, Bool.xor key secret)

end Lax755887.ReusedKey
end
