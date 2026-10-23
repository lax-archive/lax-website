-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Sum

-- Lax17.TerminalConnectivity
section
namespace Lax17.TerminalConnectivity.EdgeIndexedGraph.ElementLinkage
end Lax17.TerminalConnectivity.EdgeIndexedGraph.ElementLinkage

namespace Lax17.TerminalConnectivity.EdgeIndexedGraph.IsContraction
end Lax17.TerminalConnectivity.EdgeIndexedGraph.IsContraction

namespace Lax17.TerminalConnectivity

universe u v

/-- A finite loopless undirected multigraph with named edge copies. -/
structure EdgeIndexedGraph (V : Type u) where
  Edge : Type
  [edgeFintype : Fintype Edge]
  [edgeDecidableEq : DecidableEq Edge]
  left : Edge → V
  right : Edge → V
  end_ne : ∀ e : Edge, left e ≠ right e

namespace EdgeIndexedGraph

instance {V : Type u} (H : EdgeIndexedGraph V) : Fintype H.Edge :=
  H.edgeFintype

/-- A named edge has exactly one endpoint in `S`. -/
def Crosses {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) (S : Finset V) (e : H.Edge) : Prop :=
  (H.left e ∈ S ∧ H.right e ∉ S) ∨
    (H.right e ∈ S ∧ H.left e ∉ S)

/-- The named edge boundary of `S`. -/
noncomputable def boundary {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (S : Finset V) : Finset H.Edge :=
  @Finset.filter H.Edge (H.Crosses S) (Classical.decPred _) Finset.univ

namespace ElementCut

end ElementCut

/-- Two distinct named edges incident with `s`, with their other endpoints. -/
structure SplitPair {V : Type u} (H : EdgeIndexedGraph V) (s : V) where
  first : H.Edge
  second : H.Edge
  edge_ne : first ≠ second
  firstOther : V
  secondOther : V
  first_ends :
    (H.left first = s ∧ H.right first = firstOther) ∨
      (H.right first = s ∧ H.left first = firstOther)
  second_ends :
    (H.left second = s ∧ H.right second = secondOther) ∨
      (H.right second = s ∧ H.left second = secondOther)

/-- Edge names surviving or created by a split-off.  The right summand is
inhabited exactly when the newly created edge is not a loop. -/
def SplitEdge
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V} {s : V}
    (p : H.SplitPair s) : Type :=
  {e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕
    {_unit : Unit // p.firstOther ≠ p.secondOther}

noncomputable instance splitEdgeFintype
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V} {s : V}
    (p : H.SplitPair s) : Fintype (SplitEdge p) :=
  letI : Fintype {e : H.Edge // e ≠ p.first ∧ e ≠ p.second} :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype {_unit : Unit // p.firstOther ≠ p.secondOther} :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  inferInstanceAs
    (Fintype
      ({e : H.Edge // e ≠ p.first ∧ e ≠ p.second} ⊕
        {_unit : Unit // p.firstOther ≠ p.secondOther}))

noncomputable instance splitEdgeDecidableEq
    {V : Type u} [DecidableEq V] {H : EdgeIndexedGraph V} {s : V}
    (p : H.SplitPair s) : DecidableEq (SplitEdge p) :=
  Classical.decEq (SplitEdge p)

/-- Split off a pair of edges at `s`, discarding a newly created loop. -/
noncomputable def splitOff {V : Type u} [DecidableEq V]
    (H : EdgeIndexedGraph V) {s : V}
    (p : H.SplitPair s) : EdgeIndexedGraph V where
  Edge := SplitEdge p
  left
    | Sum.inl e => H.left e.1
    | Sum.inr _ => p.firstOther
  right
    | Sum.inl e => H.right e.1
    | Sum.inr _ => p.secondOther
  end_ne
    | Sum.inl e => H.end_ne e.1
    | Sum.inr e => e.2

/-- `u` and `v` cannot be separated by fewer than `k` edge copies. -/
def PairEdgeConnectedAtLeast
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) (u v : V) (k : ℕ) : Prop :=
  ∀ S : Finset V, u ∈ S → v ∉ S → k ≤ (H.boundary S).card

/-- Splitting `p` preserves every local edge-connectivity value away from its
centre. -/
def IsMaderAdmissible
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : EdgeIndexedGraph V) {s : V} (p : H.SplitPair s) : Prop :=
  ∀ u v : V, u ≠ s → v ≠ s → u ≠ v → ∀ k : ℕ,
    H.PairEdgeConnectedAtLeast u v k ↔
      (H.splitOff p).PairEdgeConnectedAtLeast u v k

namespace Path

end Path

end EdgeIndexedGraph

end Lax17.TerminalConnectivity
end
