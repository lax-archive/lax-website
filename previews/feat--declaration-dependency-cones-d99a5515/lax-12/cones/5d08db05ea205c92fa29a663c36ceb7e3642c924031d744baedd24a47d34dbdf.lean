-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

-- Lax12.GraphClasses
section
namespace Lax12
end Lax12

namespace Lax12.GraphClasses
end Lax12.GraphClasses
end

-- Lax12.UniformQuasiWideness
section
namespace Lax12.UniformQuasiWideness

open Lax12.GraphClasses

/-- `G` with the vertices of `S` isolated: every edge incident to `S` is
removed and the vertex type is unchanged. This models `G − S`. -/
def deleteVerts {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

end Lax12.UniformQuasiWideness
end
