-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.LimitDecider
section
namespace Lax755887.LimitDecider

open Nat.Partrec (Code)

open Nat.Partrec.Code

def Accepted (fuel : ℕ) (code : Code) : Prop := (evaln fuel code 0).isSome = true

end Lax755887.LimitDecider
end
