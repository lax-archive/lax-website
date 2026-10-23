-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.TupleAveraging
section
namespace Lax323828.TupleAveraging
end Lax323828.TupleAveraging
end

-- Lax323828.TupleSampler
section
namespace Lax323828.TupleSampler

open scoped Classical

open FiniteProbability

open scoped BigOperators

/-- The value one on the event `S`, and zero outside it. -/
noncomputable def indicator {A : Type} (S : A → Prop) (a : A) : ℝ :=
  if S a then 1 else 0

/-- The average indicator after planting `a` at a uniformly chosen coordinate of a uniformly chosen tuple. -/
noncomputable def mass {A : Type} [Fintype A] (t : ℕ)
    (S : (Fin t → A) → Prop) (a : A) : ℝ :=
  𝔼 i : Fin t, 𝔼 z : Fin t → A, indicator S (Function.update z i a)

axiom bounds {A : Type} [Fintype A] [Nonempty A] (t : ℕ) (ht : 0 < t)
    (S : (Fin t → A) → Prop) (a : A) : 0 ≤ mass t S a ∧ mass t S a ≤ 1

end Lax323828.TupleSampler
end
