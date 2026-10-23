-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Relation

-- Lax362205.Reachability
section
namespace Lax362205.Reachability.search
end Lax362205.Reachability.search

set_option backward.isDefEq.respectTransparency false

namespace Lax362205.Reachability

abbrev Graph (N : ℕ) := Fin N → Fin N → Bool

inductive Walk {α : Type} (R : α → α → Prop) : ℕ → α → α → Prop
  | nil (a : α) : Walk R 0 a a
  | tail {n : ℕ} {a b c : α} : Walk R n a b → R b c → Walk R (n + 1) a c

def Within {α : Type} (R : α → α → Prop) (n : ℕ) (a b : α) : Prop :=
  ∃ k ≤ n, Walk R k a b

end Lax362205.Reachability
end

-- Lax362205.Counting
section
namespace Lax362205.Counting

open scoped Classical

open Lax362205.Reachability

/-- The vertices reachable from `a` using at most `k` directed edges. -/
noncomputable def layer {N : ℕ} (G : Graph N) (a : Fin N) (k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun v => Within (fun u v => G u v = true) k a v)

/-- A set of `c` distinct vertices, each reachable within `k` steps. -/
def Census {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (S : Finset (Fin N)) : Prop :=
  S.card = c ∧ ∀ v ∈ S, Within (fun u v => G u v = true) k a v

/-- A positive answer supplies a path; a negative answer supplies a census that has no edge to `v`. -/
def Classify {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (v : Fin N) : Bool → Prop
  | true => Within (fun u v => G u v = true) (k + 1) a v
  | false => ∃ S, Census G a k c S ∧ v ≠ a ∧ ∀ u ∈ S, G u v = false

/-- Classify every vertex for the next layer and count exactly `d` positive answers. -/
def CountStep {N : ℕ} (G : Graph N) (a : Fin N) (k c d : ℕ) : Prop :=
  ∃ answers : Fin N → Bool, (∀ v, Classify G a k c v (answers v)) ∧
    (Finset.univ.filter (fun v => answers v = true)).card = d

/-- Start with the source alone and certify the size of each successive reachable layer. -/
def CountTrace {N : ℕ} (G : Graph N) (a : Fin N) (counts : ℕ → ℕ) : Prop :=
  counts 0 = 1 ∧ ∀ k < N, CountStep G a k (counts k) (counts (k + 1))

end Lax362205.Counting
end

-- Lax362205.CountingTrace
section
namespace Lax362205.CountingTrace

open Lax362205.Reachability Counting

axiom correct {N : ℕ} (G : Graph N) (a : Fin N) (counts : ℕ → ℕ) :
  CountTrace G a counts ↔ ∀ k ≤ N, counts k = (layer G a k).card

end Lax362205.CountingTrace
end
