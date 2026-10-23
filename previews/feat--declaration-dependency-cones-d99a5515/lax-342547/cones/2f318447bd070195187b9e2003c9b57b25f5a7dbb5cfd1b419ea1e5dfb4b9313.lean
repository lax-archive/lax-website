-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.EquivFin

-- Lax342547.ConnectedMatching
section
namespace Lax342547.ConnectedMatching

universe u

variable {V : Type u}

/-- A finite matching whose edges are pairwise touching: each member is a
two-vertex clique, and distinct members are disjoint and joined by an edge. -/
def IsTouchingMatching (G : SimpleGraph V) (M : Finset (Finset V)) : Prop :=
  (∀ e ∈ M, e.card = 2 ∧ G.IsClique (e : Set V)) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
    ∃ v ∈ e, ∃ w ∈ f, G.Adj v w)

end Lax342547.ConnectedMatching
end

-- Lax342547.SampledGraph
section
namespace Lax342547.SampledGraph

universe u

def sampleGraph {Ω : Type u} (hole : Ω → Ω → Prop) (hsymm : (∀ ⦃i j⦄, hole i j → hole j i))
    {m : ℕ} (sample : Fin m → Ω) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ ¬ hole (sample i) (sample j)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, fun h' ↦ h.2 (hsymm h')⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

end Lax342547.SampledGraph
end

-- Lax342547.MatchingSamples
section
namespace Lax342547.MatchingSamples

open Lax342547.ConnectedMatching Lax342547.SampledGraph

noncomputable def oriented {V : Type} (e : Finset V) (he : e.card = 2) : Bool → V :=
  fun b => ((e.equivFinOfCardEq he).symm (if b then 1 else 0)).val

noncomputable def unitType {Ω : Type} {m : ℕ} (sample : Fin m → Ω)
    (e : Finset (Fin m)) (he : e.card = 2) : Ω × Ω :=
  (sample (oriented e he false),sample (oriented e he true))

def fourConflict {Ω : Type} (hole : Ω → Ω → Prop) (u v : Ω × Ω) : Prop :=
  hole u.1 v.1 ∧ hole u.1 v.2 ∧ hole u.2 v.1 ∧ hole u.2 v.2

axiom unit_types_independent {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    {m : ℕ} (sample : Fin m → Ω) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) : by
      classical
      exact let I := Finset.univ.image (fun e : M => unitType sample e.val (hM.1 _ e.property).1)
        (∀ u ∈ I, ¬ hole u.1 u.2) ∧ (∀ u ∈ I, ∀ v ∈ I, ¬ fourConflict hole u v)

end Lax342547.MatchingSamples
end
