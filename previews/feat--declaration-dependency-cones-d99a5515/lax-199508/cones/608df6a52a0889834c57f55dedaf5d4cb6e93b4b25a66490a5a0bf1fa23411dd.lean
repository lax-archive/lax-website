-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

-- Lax199508.GraphClasses
section
namespace Lax199508.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax199508.GraphClasses
end

-- Lax199508.UniformQuasiWideness
section
namespace Lax199508.UniformQuasiWideness

open Lax199508.GraphClasses

/-- A set of vertices is distance-`r` independent in `G` when every walk
between two distinct members is longer than `r`. -/
def DistIndependent {V : Type*} (G : SimpleGraph V) (r : ℕ) (A : Set V) : Prop :=
  A.Pairwise fun u v => ∀ p : G.Walk u v, r < p.length

/-- `G` with the vertices of `S` isolated: every edge incident to `S` is
removed and the vertex type is unchanged. This models `G − S`. -/
def deleteVerts {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

/-- A graph class is uniformly quasi-wide if for every radius `r` there
are a threshold function `N` and a separator bound `s` such that in
every member, every vertex set of size at least `N m` contains a
distance-`r` independent subset of size at least `m` after deleting at
most `s` vertices. -/
def UniformlyQuasiWide (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ (N : ℕ → ℕ) (s : ℕ),
    ∀ (m n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Set (Fin n), N m ≤ A.ncard →
        ∃ S B : Set (Fin n),
          S.ncard ≤ s ∧ B ⊆ A \ S ∧ m ≤ B.ncard ∧
          DistIndependent (deleteVerts G S) r B

end Lax199508.UniformQuasiWideness
end
