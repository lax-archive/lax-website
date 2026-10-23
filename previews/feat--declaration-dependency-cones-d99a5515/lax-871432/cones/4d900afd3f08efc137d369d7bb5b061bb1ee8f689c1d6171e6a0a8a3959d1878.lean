-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum
import Mathlib.Order.SetNotation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

-- Lax68.GraphMinors
section
namespace Lax68
end Lax68

namespace Lax68.GraphMinors
end Lax68.GraphMinors

namespace Lax68.GraphMinors.MinorModel
end Lax68.GraphMinors.MinorModel
end

-- Lax871432.Contractions
section
namespace Lax871432.Contractions

/-- A presentation of `K` as the graph obtained from `F` by contracting the edges inside the
classes of a partition of `V(F)` into connected parts. -/
structure Contraction {V W : Type*} (K : SimpleGraph W) (F : SimpleGraph V) where
  /-- The vertex of `K` a vertex of `F` is contracted to. -/
  proj : V → W
  /-- Each class induces a connected — in particular nonempty — subgraph of `F`. -/
  connected : ∀ w, (F.induce {v | proj v = w}).Connected
  /-- Distinct classes are adjacent in `K` exactly when `F` joins them. -/
  adj_iff : ∀ a b, K.Adj a b ↔ a ≠ b ∧ ∃ x y, F.Adj x y ∧ proj x = a ∧ proj y = b

/-- `K` is *obtained from `F` by contracting edges*. -/
def IsContraction {V W : Type*} (K : SimpleGraph W) (F : SimpleGraph V) : Prop :=
  Nonempty (Contraction K F)

end Lax871432.Contractions
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

/-- `𝓕` is *closed under contracting edges* if every quotient of a member by a partition into
connected parts is a member. -/
def IsContractionClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} (K : SimpleGraph W),
    IsContraction K F → 𝓕.Mem F → 𝓕.Mem K

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

end Lax871432.DistinguishingClosure
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

-- Lax871432.PreservationProperties
section
open Lax871432.GraphProducts Lax871432.IsomorphismRelaxations

open scoped Lax871432.GraphProducts

namespace Lax871432.PreservationProperties

/-- `R` is *preserved under right lexicographic products*: multiplying on the right by a fixed
graph keeps related graphs related. -/
def PreservedUnderRightLexProd (R : GraphIsoRelaxation) : Prop :=
  ∀ {V V' W : Type} [Finite V] [Finite V'] [Finite W]
    (G : SimpleGraph V) (G' : SimpleGraph V') (H : SimpleGraph W),
    R.Rel G G' → R.Rel (lexProd G H) (lexProd G' H)

end Lax871432.PreservationProperties
end

-- Lax871432.EdgeContractions
section
open Lax871432.ClosureProperties Lax871432.DistinguishingClosure

open Lax871432.GraphClasses

open Lax871432.HomomorphismIndistinguishability Lax871432.PreservationProperties

namespace Lax871432.EdgeContractions

/-- **(2) $\Leftrightarrow$ (3).** -/
axiom preservedUnderRightLexProd_iff_cl_isContractionClosed (𝓕 : GraphClass) :
    PreservedUnderRightLexProd (homIndRel 𝓕) ↔ IsContractionClosed (cl 𝓕)

end Lax871432.EdgeContractions
end
