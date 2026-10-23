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
end Lax253009.TupleAveraging
end

-- Lax253009.TupleSampler
section
namespace Lax253009.TupleSampler

open FiniteProbability

open scoped BigOperators

noncomputable def indicator {A : Type} (S : A → Prop) (a : A) : ℝ := by
  classical
  exact if S a then 1 else 0

noncomputable def mass {A : Type} [Fintype A] (t : ℕ)
    (S : (Fin t → A) → Prop) (a : A) : ℝ := by
  classical
  exact 𝔼 i : Fin t, 𝔼 z : Fin t → A, indicator S (Function.update z i a)

axiom bounds {A : Type} [Fintype A] [Nonempty A] (t : ℕ) (ht : 0 < t)
    (S : (Fin t → A) → Prop) (a : A) : 0 ≤ mass t S a ∧ mass t S a ≤ 1

end Lax253009.TupleSampler
end
