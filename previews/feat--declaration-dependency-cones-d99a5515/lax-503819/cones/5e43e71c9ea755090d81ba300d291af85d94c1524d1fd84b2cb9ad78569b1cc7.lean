-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Language
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Forall2

-- Lax503819.Words
section
namespace Lax503819.Words

abbrev Position {A : Type} (w : List A) := Fin w.length

end Lax503819.Words
end

-- Lax503819.PositiveLogic
section
namespace Lax503819.PositiveLogic
end Lax503819.PositiveLogic

namespace Lax503819.PositiveLogic.Formula
end Lax503819.PositiveLogic.Formula

namespace Lax503819.PositiveLogic.Formula.Realize
end Lax503819.PositiveLogic.Formula.Realize

namespace Lax503819.PositiveLogic.Formula.conj
end Lax503819.PositiveLogic.Formula.conj

namespace Lax503819.PositiveLogic.Formula.disj
end Lax503819.PositiveLogic.Formula.disj

namespace Lax503819.PositiveLogic.Formula.exists_
end Lax503819.PositiveLogic.Formula.exists_

namespace Lax503819.PositiveLogic.Formula.falsity
end Lax503819.PositiveLogic.Formula.falsity

namespace Lax503819.PositiveLogic.Formula.forall_
end Lax503819.PositiveLogic.Formula.forall_

namespace Lax503819.PositiveLogic.Formula.le
end Lax503819.PositiveLogic.Formula.le

namespace Lax503819.PositiveLogic.Formula.letter
end Lax503819.PositiveLogic.Formula.letter

namespace Lax503819.PositiveLogic.Formula.lt
end Lax503819.PositiveLogic.Formula.lt

namespace Lax503819.PositiveLogic.Formula.truth
end Lax503819.PositiveLogic.Formula.truth
end

-- Lax503819.PositiveGames
section
namespace Lax503819.PositiveGames.Survives
end Lax503819.PositiveGames.Survives

namespace Lax503819.PositiveGames

open Lax503819.Words Lax503819.PositiveLogic

def Valid {A : Type} [LE A] {u v : List A} {k : ℕ}
    (α : Fin k → Position u) (β : Fin k → Position v) : Prop :=
  (∀ i, u.get (α i) ≤ v.get (β i)) ∧
  (∀ i j, α i ≤ α j ↔ β i ≤ β j)

end Lax503819.PositiveGames
end
