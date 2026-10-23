-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.LimitDecider
section
namespace Lax755887
end Lax755887

namespace Lax755887.LimitDecider
end Lax755887.LimitDecider
end

-- Lax755887.LimitDeciderControls
section
namespace Lax755887.LimitDeciderControls

open Lax755887.LimitDecider

open Nat.Partrec (Code)

open Nat.Partrec.Code

axiom halting_not_computable : ¬ ComputablePred (fun c : Code => (eval c 0).Dom)

end Lax755887.LimitDeciderControls
end
