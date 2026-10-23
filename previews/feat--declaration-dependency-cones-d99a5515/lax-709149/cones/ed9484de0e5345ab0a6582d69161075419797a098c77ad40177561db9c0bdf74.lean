-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finite.Defs
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

-- Lax709149.RegularTerms
section
namespace Lax709149.RegularTerms.splitList
end Lax709149.RegularTerms.splitList

namespace Lax709149.RegularTerms.RegTerm.eval
end Lax709149.RegularTerms.RegTerm.eval

namespace Lax709149.RegularTerms

open Lax709149.Types

/-- The syntax of regular terms: atomic terms and combinators. -/
inductive RegTerm : Ty → Ty → Type
  /-- Identity `A → A`. -/
  | id (A : Ty) : RegTerm A A
  /-- First projection `A × B → A`. -/
  | fst (A B : Ty) : RegTerm (.prod A B) A
  /-- Second projection `A × B → B`. -/
  | snd (A B : Ty) : RegTerm (.prod A B) B
  /-- Left co-projection `A → A + B`. -/
  | inl (A B : Ty) : RegTerm A (.sum A B)
  /-- Right co-projection `B → A + B`. -/
  | inr (A B : Ty) : RegTerm B (.sum A B)
  /-- Distributivity `A × (B + C) → (A × B) + (A × C)`. -/
  | distr (A B C : Ty) : RegTerm (.prod A (.sum B C)) (.sum (.prod A B) (.prod A C))
  /-- The list constructor `1 + A × A* → A*`. -/
  | cons (A : Ty) : RegTerm (.sum .one (.prod A (.list A))) (.list A)
  /-- The list deconstructor `A* → 1 + A × A*`. -/
  | uncons (A : Ty) : RegTerm (.list A) (.sum .one (.prod A (.list A)))
  /-- Reverse `A* → A*`. -/
  | reverse (A : Ty) : RegTerm (.list A) (.list A)
  /-- Concatenation `A** → A*`. -/
  | concat (A : Ty) : RegTerm (.list (.list A)) (.list A)
  /-- Split `(A + B)* → A* × (B × A*)*`. -/
  | split (A B : Ty) : RegTerm (.list (.sum A B)) (.prod (.list A) (.list (.prod B (.list A))))
  /-- Group prefix multiplication `G* → G*`, for a group on a finite type. -/
  | pref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) : RegTerm (.list G) (.list G)
  /-- Composition. -/
  | comp {A B C : Ty} : RegTerm A B → RegTerm B C → RegTerm A C
  /-- Pairing. -/
  | pair {A B C : Ty} : RegTerm A B → RegTerm A C → RegTerm A (.prod B C)
  /-- Co-pairing. -/
  | copair {A B C : Ty} : RegTerm A C → RegTerm B C → RegTerm (.sum A B) C
  /-- Map. -/
  | map {A B : Ty} : RegTerm A B → RegTerm (.list A) (.list B)

end Lax709149.RegularTerms
end
