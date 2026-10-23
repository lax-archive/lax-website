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

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.DecodedStrategies
section
namespace Lax323828.DecodedStrategies
end Lax323828.DecodedStrategies
end

-- Lax323828.ProjectionGames
section
namespace Lax323828.ProjectionGames

open FiniteProbability

structure System (V D A : Type) where
  reverse : V × D → V × D
  reverse_involutive : Function.Involutive reverse
  relation : V × D → A → A → Bool

namespace System

variable {V D A : Type} (C : System V D A)

def question (v : V) (ω : D × Bool) : V × D :=
  if ω.2 then C.reverse (v, ω.1) else (v, ω.1)

def project (b : Bool) (p : A × A) : A := if b then p.2 else p.1

end System

end Lax323828.ProjectionGames
end

-- Lax323828.FortifiedSquaring
section
namespace Lax323828.FortifiedSquaring
end Lax323828.FortifiedSquaring

namespace Lax323828.FortifiedSquaring.Game
end Lax323828.FortifiedSquaring.Game
end

-- Lax323828.TupleFortification
section
namespace Lax323828.TupleFortification
end Lax323828.TupleFortification
end

-- Lax323828.CenteredProjection
section
namespace Lax323828.CenteredProjection

open FiniteProbability FortifiedSquaring TupleFortification

open scoped BigOperators

structure System (U Ω W X Y : Type) where
  question : U → Ω → W
  valid : U → Ω → Y → Bool
  project : U → Ω → Y → X

namespace System

variable {U Ω W X Y : Type} (G : System U Ω W X Y)

end System

def fromConstraints {V D A : Type} (C : ProjectionGames.System V D A) :
    System V (D × Bool) (V × D) A (A × A) where
  question := C.question
  valid v ω p := C.relation (C.question v ω) p.1 p.2
  project _ ω p := ProjectionGames.System.project ω.2 p

end Lax323828.CenteredProjection
end
