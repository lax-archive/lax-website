-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Rat.Defs
import Mathlib.Order.SetNotation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

-- Lax871432.GraphClasses
section
namespace Lax871432.GraphClasses

/-- A class of finite simple graphs, given by an isomorphism-invariant predicate on the
finite simple graphs. -/
structure GraphClass where
  /-- The graphs of the class. -/
  Mem : ∀ {V : Type} [Finite V], SimpleGraph V → Prop
  /-- The class is invariant under isomorphism. -/
  mem_congr : ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} {F' : SimpleGraph W},
    Nonempty (F ≃g F') → (Mem F ↔ Mem F')

end Lax871432.GraphClasses
end

-- Lax871432.HomomorphismCounts
section
namespace Lax871432.HomomorphismCounts

/-- $\hom(F, G)$, the number of homomorphisms from `F` to `G`. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card (F →g G)

end Lax871432.HomomorphismCounts
end

-- Lax871432.IsomorphismRelaxations
section
namespace Lax871432.IsomorphismRelaxations

/-- A *graph isomorphism relaxation*: an equivalence relation on finite simple graphs which
relates any two isomorphic graphs, and is therefore invariant under isomorphism. -/
structure GraphIsoRelaxation where
  /-- The relation itself. -/
  Rel : ∀ ⦃V W : Type⦄ [Finite V] [Finite W], SimpleGraph V → SimpleGraph W → Prop
  /-- Isomorphic graphs are related; in particular the relation is reflexive. -/
  rel_of_iso : ∀ {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W},
    Nonempty (G ≃g H) → Rel G H
  /-- The relation is symmetric. -/
  symm : ∀ {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W},
    Rel G H → Rel H G
  /-- The relation is transitive. -/
  trans : ∀ {U V W : Type} [Finite U] [Finite V] [Finite W] {G : SimpleGraph U}
    {H : SimpleGraph V} {K : SimpleGraph W}, Rel G H → Rel H K → Rel G K

end Lax871432.IsomorphismRelaxations
end

-- Lax871432.HomomorphismIndistinguishability
section
open Lax871432.GraphClasses Lax871432.HomomorphismCounts Lax871432.IsomorphismRelaxations

namespace Lax871432.HomomorphismIndistinguishability

/-- *Homomorphism indistinguishability over `𝓕`*: the graph isomorphism relaxation relating
two graphs when they receive the same number of homomorphisms from every graph of `𝓕`. -/
def homIndRel (𝓕 : GraphClass) : GraphIsoRelaxation where
  Rel := @fun _ _ _ _ G H =>
    ∀ ⦃m : ℕ⦄ (F : SimpleGraph (Fin m)), 𝓕.Mem F → homCount F G = homCount F H
  rel_of_iso := by
    -- Postcomposing with the isomorphism is a bijection between the two hom-sets, so
    -- isomorphic graphs receive equally many homomorphisms from every graph.
    rintro V W _ _ G H ⟨e⟩ m F -
    exact Nat.card_congr
      { toFun f := e.toHom.comp f
        invFun f := e.symm.toHom.comp f
        left_inv _ := by ext a; simp
        right_inv _ := by ext a; simp }
  symm := by
    intro V W _ _ G H h m F hF
    exact (h F hF).symm
  trans := by
    intro U V W _ _ _ G H K h h' m F hF
    exact (h F hF).trans (h' F hF)

@[inherit_doc homIndRel]
scoped notation:50 G " ≡[" 𝓕 "] " H => GraphIsoRelaxation.Rel (homIndRel 𝓕) G H

end Lax871432.HomomorphismIndistinguishability
end

-- Lax871432.DistinguishingClosure
section
open Lax871432.GraphClasses

open Lax871432.HomomorphismCounts Lax871432.HomomorphismIndistinguishability

open Lax871432.IsomorphismRelaxations

open scoped Lax871432.HomomorphismIndistinguishability

namespace Lax871432.DistinguishingClosure

/-- The relaxation `R` *determines* the homomorphism counts of `K` if related graphs receive
equally many homomorphisms from `K`. -/
structure Determines (R : GraphIsoRelaxation) {U : Type} [Finite U] (K : SimpleGraph U) :
    Prop where
  /-- Graphs related by `R` receive equally many homomorphisms from `K`. -/
  homCount_eq : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
    R.Rel G H → homCount K G = homCount K H

end Lax871432.DistinguishingClosure
end

-- Lax871432.GraphFamilies
section
namespace Lax871432.GraphFamilies

/-- An *indexed graph family* of order `n`: a family of simple graphs indexed by `ι`, the
`i`-th of which has vertex set `Fin (size i)` for some `size i ≤ n`. -/
structure GraphFamily (n : ℕ) (ι : Type*) where
  /-- The number of vertices of the `i`-th graph. -/
  size : ι → ℕ
  /-- Every graph in the family has at most `n` vertices. -/
  size_le : ∀ i, size i ≤ n
  /-- The `i`-th graph of the family. -/
  graph : ∀ i, SimpleGraph (Fin (size i))

variable {n : ℕ} {ι : Type*}

/-- Two indices carry isomorphic graphs. -/
def GraphFamily.Iso (F : GraphFamily n ι) (i j : ι) : Prop :=
  Nonempty (F.graph i ≃g F.graph j)

/-- The graphs in the family are pairwise non-isomorphic. -/
def GraphFamily.PairwiseNonIso (F : GraphFamily n ι) : Prop :=
  Pairwise fun i j => ¬ F.Iso i j

end Lax871432.GraphFamilies
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

end Lax871432.GraphProducts
end

-- Lax871432.PreservationProperties
section
open Lax871432.GraphProducts Lax871432.IsomorphismRelaxations

open scoped Lax871432.GraphProducts

namespace Lax871432.PreservationProperties

/-- `R` is *preserved under categorical products*: multiplying both sides by a fixed graph
keeps them related. -/
def PreservedUnderCatProd (R : GraphIsoRelaxation) : Prop :=
  ∀ {V W X : Type} [Finite V] [Finite W] [Finite X]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : SimpleGraph X),
    R.Rel G H → R.Rel (G ×g K) (H ×g K)

end Lax871432.PreservationProperties
end

-- Lax871432.LinearCombinationLemma
section
open Lax871432.DistinguishingClosure Lax871432.GraphFamilies Lax871432.HomomorphismCounts

open Lax871432.IsomorphismRelaxations Lax871432.PreservationProperties

namespace Lax871432.LinearCombinationLemma

/-- A relaxation preserved under categorical products which determines a linear combination of
homomorphism counts, over pairwise non-isomorphic graphs and with nonzero coefficients,
determines each of its constituents. -/
axiom determines_of_determines_sum (R : GraphIsoRelaxation) (hprod : PreservedUnderCatProd R)
    {n : ℕ} {ι : Type} [Fintype ι] (L : GraphFamily n ι) (hL : L.PairwiseNonIso)
    (α : ι → ℚ) (hα : ∀ i, α i ≠ 0)
    (hdet : ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
      R.Rel G H →
        ∑ i, α i * (homCount (L.graph i) G : ℚ) = ∑ i, α i * (homCount (L.graph i) H : ℚ))
    (i : ι) : Determines R (L.graph i)

end Lax871432.LinearCombinationLemma
end
