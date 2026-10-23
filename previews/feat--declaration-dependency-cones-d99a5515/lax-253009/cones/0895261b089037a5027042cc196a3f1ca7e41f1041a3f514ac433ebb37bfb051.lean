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

end Lax253009.FortifiedSquaring
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

def symmetrize : Game (U × (Ω × Ω)) W Y X where
  left z := G.question z.1 z.2.1
  right z := G.question z.1 z.2.2
  validLeft z y := G.valid z.1 z.2.1 y
  validRight z y := G.valid z.1 z.2.2 y
  projectLeft z y := G.project z.1 z.2.1 y
  projectRight z y := G.project z.1 z.2.2 y

end System

end Lax253009.CenteredProjection
end
