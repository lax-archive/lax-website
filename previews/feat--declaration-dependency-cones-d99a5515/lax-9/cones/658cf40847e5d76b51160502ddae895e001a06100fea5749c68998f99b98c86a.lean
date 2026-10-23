-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax9.MergeWidth
section
namespace Lax9.MergeWidth

open scoped Classical

universe u

variable {V : Type u} [Fintype V]

/--
A **merge sequence** for a finite simple graph $G$ is a sequence
$(P₁, R₁), …, (P_length, R_length)$ where:

* each $part i$ is a partition of $V(G)$ (encoded as a $Setoid$), with $part 1$
  the partition into singletons ($⊥$) and $part length$ the trivial partition
  with one part ($⊤$);
* the partitions are **coarsening**: $part i ≤ part j$ for $i ≤ j$
  (recall that for setoids a *coarser* partition is a *larger* relation);
* each $resolved i$ is the graph $(V, Rᵢ)$ of **resolved pairs**, and these are
  **monotone**: $resolved i ≤ resolved j$ for $i ≤ j$;
* (**uniformity**) for any two parts $A, B$ of $part i$, the *unresolved* pairs
  between $A$ and $B$ (pairs $xy ∉ Rᵢ$) are either all edges or all non-edges of
  $G$.
-/
structure MergeSeq (G : SimpleGraph V) where
  /-- The number $m$ of steps of the sequence. -/
  length : ℕ
  /-- The sequence is nonempty. -/
  one_le_length : 1 ≤ length
  /-- The partition $Pᵢ$ at step $i$ (as a setoid on the vertices). -/
  part : ℕ → Setoid V
  /-- The graph $(V, Rᵢ)$ of resolved pairs at step $i$. -/
  resolved : ℕ → SimpleGraph V
  /-- $P₁$ is the partition into singletons. -/
  part_one : part 1 = ⊥
  /-- $P_m$ is the trivial partition with a single part. -/
  part_length : part length = ⊤
  /-- The partitions get coarser. -/
  part_mono : ∀ ⦃i j⦄, 1 ≤ i → i ≤ j → j ≤ length → part i ≤ part j
  /-- The sets of resolved pairs are monotone. -/
  resolved_mono : ∀ ⦃i j⦄, 1 ≤ i → i ≤ j → j ≤ length → resolved i ≤ resolved j
  /-- Uniformity: unresolved pairs between two parts are all edges or all
  non-edges. -/
  uniform : ∀ ⦃i⦄, 1 ≤ i → i ≤ length → ∀ ⦃x x' y y' : V⦄,
      (part i).r x x' → (part i).r y y' → x ≠ y → x' ≠ y' →
      ¬ (resolved i).Adj x y → ¬ (resolved i).Adj x' y' →
      (G.Adj x y ↔ G.Adj x' y')

namespace MergeSeq

variable {G : SimpleGraph V}

end MergeSeq

end Lax9.MergeWidth
end
