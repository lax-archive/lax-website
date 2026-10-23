-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.EquivFin

-- Lax342547.ConnectedMatching
section
namespace Lax342547
end Lax342547

namespace Lax342547.ConnectedMatching
end Lax342547.ConnectedMatching
end

-- Lax342547.SampledGraph
section
namespace Lax342547
end Lax342547

namespace Lax342547.SampledGraph
end Lax342547.SampledGraph
end

-- Lax342547.MatchingSamples
section
namespace Lax342547.MatchingSamples

open Lax342547.ConnectedMatching Lax342547.SampledGraph

def fourConflict {Ω : Type} (hole : Ω → Ω → Prop) (u v : Ω × Ω) : Prop :=
  hole u.1 v.1 ∧ hole u.1 v.2 ∧ hole u.2 v.1 ∧ hole u.2 v.2

end Lax342547.MatchingSamples
end
