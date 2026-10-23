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

-- Lax755887.LimitDeciderContract
section
namespace Lax755887.LimitDeciderContract

open Lax755887.LimitDecider

open Nat.Partrec (Code)

open Nat.Partrec.Code

axiom monotone_limit (p : ℕ → Code → Prop)
    (step : ∀ n c, p n c → p (n + 1) c)
    (deciders : ∀ n, ComputablePred (p n)) : ComputablePred (fun c => ∃ n, p n c)

end Lax755887.LimitDeciderContract
end
