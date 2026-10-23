-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.ReusedKey
section
namespace Lax755887.ReusedKey

def probability (event : Bool → Bool) : ℚ :=
  ((if event false then 1 else 0) + (if event true then 1 else 0)) / 2

end Lax755887.ReusedKey
end

-- Lax755887.ReusedKeyControls
section
namespace Lax755887.ReusedKeyControls

open Lax755887.ReusedKey

axiom complement (event : Bool → Bool) :
    probability (fun k => !(event k)) = 1 - probability event

end Lax755887.ReusedKeyControls
end
