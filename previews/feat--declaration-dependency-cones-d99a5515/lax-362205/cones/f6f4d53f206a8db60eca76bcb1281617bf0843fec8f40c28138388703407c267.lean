-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.FinRange
import Mathlib.Logic.Relation

-- Lax362205.Reachability
section
namespace Lax362205.Reachability.Walk
end Lax362205.Reachability.Walk

namespace Lax362205.Reachability.search
end Lax362205.Reachability.search

set_option backward.isDefEq.respectTransparency false

namespace Lax362205.Reachability

abbrev Graph (N : ℕ) := Fin N → Fin N → Bool

def Reachable {N : ℕ} (G : Graph N) (a b : Fin N) : Prop :=
  Relation.ReflTransGen (fun u v => G u v = true) a b

end Lax362205.Reachability
end
