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
end Lax323828.ProjectionGames

namespace Lax323828.ProjectionGames.System
end Lax323828.ProjectionGames.System
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

def tensor : System (U × U) (Ω × Ω) (W × W) (X × X) (Y × Y) where
  question u ω := (G.question u.1 ω.1, G.question u.2 ω.2)
  valid u ω y := G.valid u.1 ω.1 y.1 && G.valid u.2 ω.2 y.2
  project u ω y := (G.project u.1 ω.1 y.1, G.project u.2 ω.2 y.2)

end System

end Lax323828.CenteredProjection
end
