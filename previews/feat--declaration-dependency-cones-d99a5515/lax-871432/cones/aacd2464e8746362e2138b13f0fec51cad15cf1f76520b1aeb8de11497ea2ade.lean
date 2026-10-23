-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

-- Lax871432.ConnectedPartitions
section
namespace Lax871432.ConnectedPartitions

variable {V : Type*}

/-- A partition of the vertices of `F`, all of whose classes induce connected subgraphs. -/
structure ConnPart (F : SimpleGraph V) where
  /-- The partition, as an equivalence relation on the vertices. -/
  setoid : Setoid V
  /-- Every class induces a connected subgraph of `F`. -/
  connected : ∀ a : Quotient setoid, (F.induce {v | Quotient.mk setoid v = a}).Connected

namespace ConnPart

variable {F : SimpleGraph V} (𝓡 : ConnPart F)

/-- The class of a vertex. -/
def proj (v : V) : Quotient 𝓡.setoid := Quotient.mk 𝓡.setoid v

/-- `∐ R ∈ 𝓡, F[R]`, the disjoint union of the subgraphs induced by the classes. -/
def parts : SimpleGraph (Σ a : Quotient 𝓡.setoid, {v | 𝓡.proj v = a}) where
  Adj p q := F.Adj p.2.1 q.2.1 ∧ 𝓡.proj p.2.1 = 𝓡.proj q.2.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => F.irrefl h.1⟩

end ConnPart

end Lax871432.ConnectedPartitions
end
