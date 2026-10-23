-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.FinRange
import Mathlib.Logic.Relation

-- Lax733996.Reachability
section
namespace Lax733996.Reachability.search
end Lax733996.Reachability.search

set_option backward.isDefEq.respectTransparency false

namespace Lax733996.Reachability

inductive Walk {α : Type} (R : α → α → Prop) : ℕ → α → α → Prop
  | nil (a : α) : Walk R 0 a a
  | tail {n : ℕ} {a b c : α} : Walk R n a b → R b c → Walk R (n + 1) a c

def Within {α : Type} (R : α → α → Prop) (n : ℕ) (a b : α) : Prop :=
  ∃ k ≤ n, Walk R k a b

end Lax733996.Reachability
end
