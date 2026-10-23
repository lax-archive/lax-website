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

/-- The quotient `F / 𝓡`: distinct classes are adjacent when `F` joins them. -/
def quotientGraph : SimpleGraph (Quotient 𝓡.setoid) where
  Adj a b := a ≠ b ∧ ∃ x y, F.Adj x y ∧ 𝓡.proj x = a ∧ 𝓡.proj y = b
  symm := ⟨fun _ _ h => by
    obtain ⟨hne, x, y, hxy, hx, hy⟩ := h
    exact ⟨hne.symm, y, x, hxy.symm, hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end ConnPart

end Lax871432.ConnectedPartitions
end
