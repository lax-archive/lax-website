-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum
import Mathlib.Order.SetNotation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

-- Lax68.GraphMinors
section
set_option autoImplicit false

namespace Lax68.GraphMinors

structure MinorModel {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  branchSet : W → Set V
  connected : ∀ w, (G.induce (branchSet w)).Connected
  disjoint :
    ∀ {u v}, u ≠ v →
      Disjoint (branchSet u) (branchSet v)
  adjacent :
    ∀ {u v}, H.Adj u v →
      ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y

def IsMinor {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (MinorModel H G)

end Lax68.GraphMinors
end

-- Lax871432.Contractions
section
namespace Lax871432
end Lax871432

namespace Lax871432.Contractions
end Lax871432.Contractions

namespace Lax871432.Contractions.Contraction
end Lax871432.Contractions.Contraction
end

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

-- Lax871432.ClosureProperties
section
open Lax871432.Contractions Lax871432.GraphClasses

namespace Lax871432.ClosureProperties

/-- `𝓕` is *union-closed* if the disjoint union of two members is a member. -/
def IsUnionClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] (F₁ : SimpleGraph V) (F₂ : SimpleGraph W),
    𝓕.Mem F₁ → 𝓕.Mem F₂ → 𝓕.Mem (F₁ ⊕g F₂)

/-- `𝓕` is *minor-closed* if every minor of a member is a member. -/
def IsMinorClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} (K : SimpleGraph W),
    Lax68.GraphMinors.IsMinor K F → 𝓕.Mem F → 𝓕.Mem K

end Lax871432.ClosureProperties
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

/-- `𝓕` is *homomorphism distinguishing closed* if it contains its own closure, i.e. if
adding any graph to `𝓕` strictly refines $\equiv_{\mathcal{F}}$. -/
def IsHomDistinguishingClosed (𝓕 : GraphClass) : Prop :=
  ∀ ⦃V : Type⦄ [Finite V] (F : SimpleGraph V), (cl 𝓕).Mem F → 𝓕.Mem F

end Lax871432.DistinguishingClosure
end

-- Lax871432.RobersonConjecture
section
open Lax871432.ClosureProperties Lax871432.DistinguishingClosure

open Lax871432.GraphClasses

namespace Lax871432.RobersonConjecture

/-- **Roberson's conjecture.** Every nonempty, minor-closed, union-closed class of finite
simple graphs is homomorphism distinguishing closed. -/
axiom isHomDistinguishingClosed_of_isMinorClosed_of_isUnionClosed (𝓕 : GraphClass)
    (hne : ∃ (n : ℕ) (F : SimpleGraph (Fin n)), 𝓕.Mem F) :
    IsMinorClosed 𝓕 → IsUnionClosed 𝓕 → IsHomDistinguishingClosed 𝓕

end Lax871432.RobersonConjecture
end
