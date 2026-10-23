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

noncomputable def oriented {V : Type} (e : Finset V) (he : e.card = 2) : Bool → V :=
  fun b => ((e.equivFinOfCardEq he).symm (if b then 1 else 0)).val

noncomputable def unitType {Ω : Type} {m : ℕ} (sample : Fin m → Ω)
    (e : Finset (Fin m)) (he : e.card = 2) : Ω × Ω :=
  (sample (oriented e he false),sample (oriented e he true))

end Lax342547.MatchingSamples
end
