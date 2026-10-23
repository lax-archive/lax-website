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
end Lax253009.ProjectionGames

namespace Lax253009.ProjectionGames.System
end Lax253009.ProjectionGames.System
end

-- Lax253009.FortifiedSquaring
section
namespace Lax253009.FortifiedSquaring
end Lax253009.FortifiedSquaring

namespace Lax253009.FortifiedSquaring.Game
end Lax253009.FortifiedSquaring.Game
end

-- Lax253009.TupleFortification
section
namespace Lax253009.TupleFortification
end Lax253009.TupleFortification
end

-- Lax253009.CenteredProjection
section
namespace Lax253009.CenteredProjection

open FiniteProbability FortifiedSquaring TupleFortification

open scoped BigOperators

structure System (U Ω W X Y : Type) where
  question : U → Ω → W
  valid : U → Ω → Y → Bool
  project : U → Ω → Y → X

namespace System

variable {U Ω W X Y : Type} (G : System U Ω W X Y)

def tensor : System (U × U) (Ω × Ω) (W × W) (X × X) (Y × Y) where
  question u ω := (G.question u.1 ω.1, G.question u.2 ω.2)
  valid u ω y := G.valid u.1 ω.1 y.1 && G.valid u.2 ω.2 y.2
  project u ω y := (G.project u.1 ω.1 y.1, G.project u.2 ω.2 y.2)

end System

end Lax253009.CenteredProjection
end
