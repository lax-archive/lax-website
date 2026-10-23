-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.PNat.Basic
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
end Lax253009.CenteredProjection

namespace Lax253009.CenteredProjection.System
end Lax253009.CenteredProjection.System
end

-- Lax253009.Amplification
section
namespace Lax253009.Amplification.Scheme.centers
end Lax253009.Amplification.Scheme.centers

namespace Lax253009.Amplification.Scheme.centersNonempty
end Lax253009.Amplification.Scheme.centersNonempty

namespace Lax253009.Amplification

open CenteredProjection TupleFortification

open scoped BigOperators

inductive Scheme where
  | base
  | step (t : ℕ+) (previous : Scheme)

namespace Scheme

end Scheme

end Lax253009.Amplification
end
