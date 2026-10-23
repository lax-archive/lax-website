-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.TupleAveraging
section
namespace Lax253009.TupleAveraging

open scoped BigOperators

axiom restriction_correlation {A : Type} [Fintype A] [Nonempty A]
    (t : ℕ) (ht : 0 < t) (f : A → ℝ) (hf : ∀ a, |f a| ≤ 1)
    (S : (Fin t → A) → Prop) [DecidablePred S] :
    |𝔼 z : Fin t → A, if S z then (𝔼 i, f (z i)) - (𝔼 a, f a) else 0| ^ 2 ≤
      1 / (t : ℝ)

end Lax253009.TupleAveraging
end
