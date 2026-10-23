-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.FinRange
import Mathlib.Logic.Relation

-- Lax733996.Reachability
section
namespace Lax733996.Reachability.Walk
end Lax733996.Reachability.Walk

namespace Lax733996.Reachability.search
end Lax733996.Reachability.search

set_option backward.isDefEq.respectTransparency false

namespace Lax733996.Reachability

abbrev Graph (N : ℕ) := Fin N → Fin N → Bool

def Reachable {N : ℕ} (G : Graph N) (a b : Fin N) : Prop :=
  Relation.ReflTransGen (fun u v => G u v = true) a b

end Lax733996.Reachability
end
