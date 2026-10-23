-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite

-- Lax871432.LoopGraphs
section
namespace Lax871432.LoopGraphs

variable {U V W : Type*}

/-- A graph in which loops are allowed: a symmetric relation on the vertex type.  Contrast
with `SimpleGraph`, which additionally requires irreflexivity, and with `Digraph`, which
requires nothing. -/
@[ext]
structure LoopGraph (V : Type*) where
  /-- The adjacency relation.  A vertex may be adjacent to itself, i.e. carry a loop. -/
  Adj : V → V → Prop
  /-- The adjacency relation is symmetric. -/
  symm : Std.Symm Adj := by aesop

namespace LoopGraph

/-- A homomorphism of loop graphs is a map preserving adjacency; loops are therefore sent to
loops, and edges to edges or to loops. -/
abbrev Hom (X : LoopGraph V) (Y : LoopGraph W) := X.Adj →r Y.Adj

/-- An isomorphism of loop graphs. -/
abbrev Iso (X : LoopGraph V) (Y : LoopGraph W) := X.Adj ≃r Y.Adj

end LoopGraph

@[inherit_doc LoopGraph.Hom] scoped infixl:50 " →lg " => Lax871432.LoopGraphs.LoopGraph.Hom

@[inherit_doc LoopGraph.Iso] scoped infixl:50 " ≃lg " => Lax871432.LoopGraphs.LoopGraph.Iso

namespace LoopGraph

/-- The *full complement* of `X`: every edge becomes a non-edge and every loop a non-loop. -/
def fullCompl (X : LoopGraph V) : LoopGraph V where
  Adj u v := ¬ X.Adj u v
  symm := ⟨fun _ _ h h' => h (X.symm.symm _ _ h')⟩

end LoopGraph

/-- The *contraction quotient* `F ⊘ L`: its vertices are the connected components of the graph
on `V(F)` with edge set `L`, and `[v]` is adjacent to `[w]` when some edge of `E(F) \ L` joins
a vertex of `[v]` to a vertex of `[w]`.

The result may have loops, so it is a `LoopGraph`. -/
def contractionQuotient (F : SimpleGraph V) (L : Set (Sym2 V)) :
    LoopGraph (SimpleGraph.fromEdgeSet L).ConnectedComponent where
  Adj c d := ∃ x y, F.Adj x y ∧ s(x, y) ∉ L ∧
    (SimpleGraph.fromEdgeSet L).connectedComponentMk x = c ∧
    (SimpleGraph.fromEdgeSet L).connectedComponentMk y = d
  symm := ⟨fun _ _ ⟨x, y, hxy, hL, hx, hy⟩ =>
    ⟨y, x, hxy.symm, Sym2.eq_swap ▸ hL, hy, hx⟩⟩

@[inherit_doc] scoped notation:70 F:70 " ⊘ " L:71 => Lax871432.LoopGraphs.contractionQuotient F L

end Lax871432.LoopGraphs
end
