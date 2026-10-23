-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

-- Lax709149.Types
section
namespace Lax709149.Types.Ty
end Lax709149.Types.Ty

namespace Lax709149.Types.joinSep
end Lax709149.Types.joinSep

namespace Lax709149.Types.Ty.Elt
end Lax709149.Types.Ty.Elt

namespace Lax709149.Types.Ty.list
end Lax709149.Types.Ty.list

namespace Lax709149.Types.Ty.one
end Lax709149.Types.Ty.one

namespace Lax709149.Types.Ty.prod
end Lax709149.Types.Ty.prod

namespace Lax709149.Types.Ty.repr
end Lax709149.Types.Ty.repr

namespace Lax709149.Types.Ty.sum
end Lax709149.Types.Ty.sum

namespace Lax709149.Types

/-- The alphabet with eight letters `(`, `)`, `[`, `]`, `,`, `1`, `L`, `R`. -/
inductive Sym8 : Type
  | lpar | rpar | lbrack | rbrack | comma | one | left | right
  deriving DecidableEq

end Lax709149.Types
end
