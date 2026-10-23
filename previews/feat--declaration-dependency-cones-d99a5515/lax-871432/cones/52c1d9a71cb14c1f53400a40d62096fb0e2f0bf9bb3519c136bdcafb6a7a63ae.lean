-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.SetTheory.Cardinal.Finite

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

/-- `∐ R ∈ 𝓡, F[R]`, the disjoint union of the subgraphs induced by the classes. -/
def parts : SimpleGraph (Σ a : Quotient 𝓡.setoid, {v | 𝓡.proj v = a}) where
  Adj p q := F.Adj p.2.1 q.2.1 ∧ 𝓡.proj p.2.1 = 𝓡.proj q.2.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => F.irrefl h.1⟩

/-- A finite graph has finitely many partitions into connected parts. -/
instance instFinite [Finite V] : Finite (ConnPart F) :=
  Finite.of_injective (fun 𝓡 => (𝓡.setoid.r : V → V → Prop)) <| by
    intro R S h
    obtain ⟨s, hs⟩ := R
    obtain ⟨t, ht⟩ := S
    obtain rfl : s = t := Setoid.ext fun a b => Eq.to_iff (congrFun (congrFun h a) b)
    rfl

noncomputable instance instFintype [Finite V] : Fintype (ConnPart F) := Fintype.ofFinite _

end ConnPart

end Lax871432.ConnectedPartitions
end

-- Lax871432.GraphProducts
section
namespace Lax871432.GraphProducts

variable {α β : Type*}

/-- The *categorical product* of simple graphs: it relates `(a₁, b₁)` and `(a₂, b₂)` when `G`
relates `a₁` and `a₂` and `H` relates `b₁` and `b₂`. Contrast with `SimpleGraph.boxProd`. -/
def catProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

@[inherit_doc]
scoped infixl:70 " ×g " => catProd

/-- The *lexicographic product* of simple graphs: it relates `(a₁, b₁)` and `(a₂, b₂)` when `G`
relates `a₁` and `a₂`, or when `a₁ = a₂` and `H` relates `b₁` and `b₂`. -/
def lexProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∨ (x.1 = y.1 ∧ H.Adj x.2 y.2)
  symm := ⟨fun _ _ h => h.imp SimpleGraph.Adj.symm fun h' => ⟨h'.1.symm, h'.2.symm⟩⟩
  loopless := ⟨fun _ h => h.elim (G.irrefl ·) fun h' => H.irrefl h'.2⟩

end Lax871432.GraphProducts
end

-- Lax871432.HomomorphismCounts
section
namespace Lax871432.HomomorphismCounts

/-- $\hom(F, G)$, the number of homomorphisms from `F` to `G`. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card (F →g G)

end Lax871432.HomomorphismCounts
end

-- Lax871432.LexicographicProductCounts
section
open Lax871432.ConnectedPartitions Lax871432.GraphProducts Lax871432.HomomorphismCounts

namespace Lax871432.LexicographicProductCounts

/-- **Homomorphisms into a lexicographic product**: they are counted by the partitions of the
source into connected parts, a homomorphism from the quotient into the left factor and a
homomorphism from the disjoint union of the parts into the right factor. -/
axiom homCount_lexProd {U V W : Type*} [Finite U] [Finite V] [Finite W] (F : SimpleGraph U)
    (G : SimpleGraph V) (H : SimpleGraph W) :
    homCount F (lexProd G H) =
      ∑ 𝓡 : ConnPart F, homCount 𝓡.quotientGraph G * homCount 𝓡.parts H

end Lax871432.LexicographicProductCounts
end
