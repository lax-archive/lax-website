-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Floor

-- Lax263307.GraphClasses
section
namespace Lax263307.GraphClasses

/-- A class of finite simple graphs, represented on numbered vertex sets. -/
abbrev GraphClass := (n : ℕ) → Set (SimpleGraph (Fin n))

/-- Every graph that embeds as an induced subgraph of a member also belongs. -/
def IsHereditary (C : GraphClass) : Prop :=
  ∀ (m n : ℕ) (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)),
    G ∈ C n → Nonempty (H ↪g G) → H ∈ C m

end Lax263307.GraphClasses
end

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307
end Lax263307

namespace Lax263307.WeightedIndependentSet
end Lax263307.WeightedIndependentSet

namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance
end

-- Lax263307.IndependentBlowUp
section
namespace Lax263307.IndependentBlowUp
end Lax263307.IndependentBlowUp
end

-- Lax263307.BlowUpClasses
section
namespace Lax263307.BlowUpClasses

open GraphClasses IndependentBlowUp

/-- Graphs obtained by independent blow-ups of members, allowing empty fibres. -/
def blowUpClass (C : GraphClass) : GraphClass :=
  fun m => {H | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ C n ∧
    ∃ projection : Fin m → Fin n,
      ∀ u v, H.Adj u v ↔ G.Adj (projection u) (projection v)}

/-- Restricting an independent blow-up to any induced subgraph remains a blow-up. -/
axiom hereditary_closure (C : GraphClass) : IsHereditary (blowUpClass C)

end Lax263307.BlowUpClasses
end
