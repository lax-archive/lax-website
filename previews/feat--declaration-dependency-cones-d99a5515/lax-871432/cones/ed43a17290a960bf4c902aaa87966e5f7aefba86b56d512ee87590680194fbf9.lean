-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Maps
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

/-- Inclusion of graph classes: `𝓕 ≤ 𝓕'` if every graph in `𝓕` is in `𝓕'`. -/
instance : PartialOrder GraphClass where
  le 𝓕 𝓕' := ∀ ⦃V : Type⦄ [Finite V] (F : SimpleGraph V), 𝓕.Mem F → 𝓕'.Mem F
  le_refl _ _ _ _ hF := hF
  le_trans _ _ _ h h' _ _ F hF := h' F (h F hF)
  le_antisymm := by
    rintro ⟨Mem, _⟩ ⟨Mem', _⟩ h h'
    have : @Mem = @Mem' := by
      funext V _ F
      exact propext ⟨h F, h' F⟩
    subst this
    rfl

/-- The intersection of a set of graph classes: the graphs lying in each of them. The
intersection of a family is written `⨅ i, 𝓕 i`. -/
instance : InfSet GraphClass where
  sInf S :=
    { Mem F := ∀ 𝓕 ∈ S, 𝓕.Mem F
      mem_congr he :=
        forall_congr' fun 𝓕 : GraphClass => imp_congr_right fun _ => 𝓕.mem_congr he }

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

/-- $\mathrm{cl}(\mathcal{F})$, the homomorphism distinguishing closure of `𝓕`. -/
def cl (𝓕 : GraphClass) : GraphClass where
  Mem K := Determines (homIndRel 𝓕) K
  mem_congr {_ _ _ _ F F'} he := by
    -- Precomposition with the isomorphism is a bijection between the homomorphisms out of
    -- `F` and those out of `F'`, so the two are counted alike into every target.
    obtain ⟨e⟩ := he
    have key : ∀ {W : Type} (K : SimpleGraph W), homCount F K = homCount F' K := fun K =>
      Nat.card_congr
        { toFun f := f.comp e.symm.toHom
          invFun f := f.comp e.toHom
          left_inv _ := by ext a; exact congrArg _ (e.symm_apply_apply a)
          right_inv _ := by ext a; exact congrArg _ (e.apply_symm_apply a) }
    constructor <;> intro h <;> refine ⟨fun G H hGH => ?_⟩
    · rw [← key G, ← key H]; exact h.homCount_eq G H hGH
    · rw [key G, key H]; exact h.homCount_eq G H hGH

end Lax871432.DistinguishingClosure
end

-- Lax871432.IntersectionsUnions
section
open Lax871432.DistinguishingClosure Lax871432.GraphClasses

namespace Lax871432.IntersectionsUnions

/-- The closure of an intersection is contained in the intersection of the closures. -/
axiom cl_iInf_le_iInf_cl {I : Type*} (𝓕 : I → GraphClass) :
    cl (⨅ i, 𝓕 i) ≤ ⨅ i, cl (𝓕 i)

end Lax871432.IntersectionsUnions
end
