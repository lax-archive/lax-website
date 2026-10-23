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

open FiniteProbability

structure Game (Z W A B : Type) where
  left : Z → W
  right : Z → W
  validLeft : Z → A → Bool
  validRight : Z → A → Bool
  projectLeft : Z → A → B
  projectRight : Z → A → B

namespace Game

variable {Z W A B : Type} (G : Game Z W A B)

end Game

end Lax323828.FortifiedSquaring
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

def symmetrize : Game (U × (Ω × Ω)) W Y X where
  left z := G.question z.1 z.2.1
  right z := G.question z.1 z.2.2
  validLeft z y := G.valid z.1 z.2.1 y
  validRight z y := G.valid z.1 z.2.2 y
  projectLeft z y := G.project z.1 z.2.1 y
  projectRight z y := G.project z.1 z.2.2 y

end System

end Lax323828.CenteredProjection
end
