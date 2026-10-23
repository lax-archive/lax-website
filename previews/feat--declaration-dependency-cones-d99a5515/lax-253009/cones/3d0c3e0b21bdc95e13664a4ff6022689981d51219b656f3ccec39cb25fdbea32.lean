-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.DecodedStrategies
section
namespace Lax253009.DecodedStrategies
end Lax253009.DecodedStrategies
end

-- Lax253009.ProjectionGames
section
namespace Lax253009.ProjectionGames

open FiniteProbability

structure System (V D A : Type) where
  reverse : V × D → V × D
  reverse_involutive : Function.Involutive reverse
  relation : V × D → A → A → Bool

namespace System

variable {V D A : Type} (C : System V D A)

def Violated (a : V → A) (z : V × D) : Prop :=
  C.relation z (a z.1) (a (C.reverse z).1) ≠ true

end System

end Lax253009.ProjectionGames
end
