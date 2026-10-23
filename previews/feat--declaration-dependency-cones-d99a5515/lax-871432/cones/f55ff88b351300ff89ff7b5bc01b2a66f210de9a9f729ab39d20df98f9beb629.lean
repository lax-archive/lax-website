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

/-- A finite graph has finitely many partitions into connected parts. -/
instance instFinite [Finite V] : Finite (ConnPart F) :=
  Finite.of_injective (fun 𝓡 => (𝓡.setoid.r : V → V → Prop)) <| by
    intro R S h
    obtain ⟨s, hs⟩ := R
    obtain ⟨t, ht⟩ := S
    obtain rfl : s = t := Setoid.ext fun a b => Eq.to_iff (congrFun (congrFun h a) b)
    rfl

end ConnPart

end Lax871432.ConnectedPartitions
end
