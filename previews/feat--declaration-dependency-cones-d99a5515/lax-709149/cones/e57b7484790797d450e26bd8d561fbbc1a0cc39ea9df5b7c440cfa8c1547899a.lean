-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

-- Lax709149.Types
section
namespace Lax709149.Types.Sym8
end Lax709149.Types.Sym8

namespace Lax709149.Types.joinSep
end Lax709149.Types.joinSep

namespace Lax709149.Types.Sym8.comma
end Lax709149.Types.Sym8.comma

namespace Lax709149.Types.Sym8.lbrack
end Lax709149.Types.Sym8.lbrack

namespace Lax709149.Types.Sym8.left
end Lax709149.Types.Sym8.left

namespace Lax709149.Types.Sym8.lpar
end Lax709149.Types.Sym8.lpar

namespace Lax709149.Types.Sym8.one
end Lax709149.Types.Sym8.one

namespace Lax709149.Types.Sym8.rbrack
end Lax709149.Types.Sym8.rbrack

namespace Lax709149.Types.Sym8.right
end Lax709149.Types.Sym8.right

namespace Lax709149.Types.Sym8.rpar
end Lax709149.Types.Sym8.rpar

namespace Lax709149.Types.Ty.repr
end Lax709149.Types.Ty.repr

namespace Lax709149.Types

/-- A type: built from the unit type by product, co-product and list. -/
inductive Ty : Type
  | one : Ty
  | prod : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  | list : Ty → Ty
  deriving DecidableEq

/-- The set of elements of a type. -/
def Ty.Elt : Ty → Type
  | .one => Unit
  | .prod A B => A.Elt × B.Elt
  | .sum A B => A.Elt ⊕ B.Elt
  | .list A => List A.Elt

end Lax709149.Types
end
