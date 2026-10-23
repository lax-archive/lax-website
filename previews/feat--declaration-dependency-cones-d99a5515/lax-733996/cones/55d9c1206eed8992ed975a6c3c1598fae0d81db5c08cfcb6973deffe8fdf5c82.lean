-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Relation

-- Lax733996.Reachability
section
namespace Lax733996.Reachability.search
end Lax733996.Reachability.search

set_option backward.isDefEq.respectTransparency false

namespace Lax733996.Reachability

abbrev Graph (N : ℕ) := Fin N → Fin N → Bool

inductive Walk {α : Type} (R : α → α → Prop) : ℕ → α → α → Prop
  | nil (a : α) : Walk R 0 a a
  | tail {n : ℕ} {a b c : α} : Walk R n a b → R b c → Walk R (n + 1) a c

def Within {α : Type} (R : α → α → Prop) (n : ℕ) (a b : α) : Prop :=
  ∃ k ≤ n, Walk R k a b

end Lax733996.Reachability
end

-- Lax733996.Counting
section
namespace Lax733996.Counting

open Lax733996.Reachability

def Census {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (S : Finset (Fin N)) : Prop :=
  S.card = c ∧ ∀ v ∈ S, Within (fun u v => G u v = true) k a v

def Classify {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (v : Fin N) : Bool → Prop
  | true => Within (fun u v => G u v = true) (k + 1) a v
  | false => ∃ S, Census G a k c S ∧ v ≠ a ∧ ∀ u ∈ S, G u v = false

def CountStep {N : ℕ} (G : Graph N) (a : Fin N) (k c d : ℕ) : Prop :=
  ∃ answers : Fin N → Bool, (∀ v, Classify G a k c v (answers v)) ∧
    (Finset.univ.filter (fun v => answers v = true)).card = d

def CountTrace {N : ℕ} (G : Graph N) (a : Fin N) (counts : ℕ → ℕ) : Prop :=
  counts 0 = 1 ∧ ∀ k < N, CountStep G a k (counts k) (counts (k + 1))

def NonreachCertificate {N : ℕ} (G : Graph N) (a b : Fin N) : Prop :=
  ∃ counts, CountTrace G a counts ∧
    ∃ S, Census G a N (counts N) S ∧ b ∉ S

end Lax733996.Counting
end
