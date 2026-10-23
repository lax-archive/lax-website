-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.ReusedKey
section
namespace Lax755887.ReusedKey

def probability (event : Bool → Bool) : ℚ :=
  ((if event false then 1 else 0) + (if event true then 1 else 0)) / 2

def transcript (secret key : Bool) : Bool × Bool := (key, Bool.xor key secret)

def success (guess : Bool × Bool → Bool) : ℚ :=
  (probability (fun k => !(guess (transcript false k))) +
    probability (fun k => guess (transcript true k))) / 2

end Lax755887.ReusedKey
end

-- Lax755887.ReusedKeyClaim
section
namespace Lax755887.ReusedKeyClaim

open Lax755887.ReusedKey

axiom every_attacker_is_unbiased : ∀ guess, success guess = 1 / 2

end Lax755887.ReusedKeyClaim
end
