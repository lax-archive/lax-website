-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Order.Lattice.Nat

-- Lax183560.ModularDecomposition
section
namespace Lax183560.ModularDecomposition

/-- A recursive modular decomposition whose nontrivial substitutions use at
most `k` parts. -/
inductive ModularDecomposition :
    (V : Type) → SimpleGraph V → ℕ → Prop where
  | atom {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ)
      (h : Fintype.card V ≤ 1) : ModularDecomposition V G k
  | substitute {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (k n : ℕ)
      (part : V → Fin n) (Q : SimpleGraph (Fin n))
      (nontrivial : 2 ≤ n)
      (surjective : Function.Surjective part)
      (cross : ∀ u v : V, part u ≠ part v →
        (G.Adj u v ↔ Q.Adj (part u) (part v)))
      (children : ∀ i : Fin n,
        ModularDecomposition {v : V // part v = i}
          (G.induce {v : V | part v = i}) k)
      (arity : Q = ⊥ ∨ Q = ⊤ ∨ n ≤ k) :
      ModularDecomposition V G k

end Lax183560.ModularDecomposition
end

-- Lax183560.ModularWidth
section
namespace Lax183560.ModularWidth

open Lax183560.ModularDecomposition

/-- Existence of a modular decomposition with substitution arity bounded by k. -/
def HasModularWidthAtMost (V : Type) (G : SimpleGraph V) (k : ℕ) : Prop :=
  ModularDecomposition V G k

/-- The least maximum arity of a non-union, non-join substitution. -/
noncomputable def modularWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k | HasModularWidthAtMost V G k}

end Lax183560.ModularWidth
end
