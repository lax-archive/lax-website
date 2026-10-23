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
namespace Lax709149
end Lax709149

namespace Lax709149.Types
end Lax709149.Types

namespace Lax709149.Types.Sym8
end Lax709149.Types.Sym8

namespace Lax709149.Types.Ty
end Lax709149.Types.Ty

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
end

-- Lax709149.RegularTerms
section
namespace Lax709149.RegularTerms.RegTerm
end Lax709149.RegularTerms.RegTerm

namespace Lax709149.RegularTerms.splitList
end Lax709149.RegularTerms.splitList

namespace Lax709149.RegularTerms.RegTerm.comp
end Lax709149.RegularTerms.RegTerm.comp

namespace Lax709149.RegularTerms.RegTerm.concat
end Lax709149.RegularTerms.RegTerm.concat

namespace Lax709149.RegularTerms.RegTerm.cons
end Lax709149.RegularTerms.RegTerm.cons

namespace Lax709149.RegularTerms.RegTerm.copair
end Lax709149.RegularTerms.RegTerm.copair

namespace Lax709149.RegularTerms.RegTerm.distr
end Lax709149.RegularTerms.RegTerm.distr

namespace Lax709149.RegularTerms.RegTerm.eval
end Lax709149.RegularTerms.RegTerm.eval

namespace Lax709149.RegularTerms.RegTerm.fst
end Lax709149.RegularTerms.RegTerm.fst

namespace Lax709149.RegularTerms.RegTerm.id
end Lax709149.RegularTerms.RegTerm.id

namespace Lax709149.RegularTerms.RegTerm.inl
end Lax709149.RegularTerms.RegTerm.inl

namespace Lax709149.RegularTerms.RegTerm.inr
end Lax709149.RegularTerms.RegTerm.inr

namespace Lax709149.RegularTerms.RegTerm.map
end Lax709149.RegularTerms.RegTerm.map

namespace Lax709149.RegularTerms.RegTerm.pair
end Lax709149.RegularTerms.RegTerm.pair

namespace Lax709149.RegularTerms.RegTerm.pref
end Lax709149.RegularTerms.RegTerm.pref

namespace Lax709149.RegularTerms.RegTerm.reverse
end Lax709149.RegularTerms.RegTerm.reverse

namespace Lax709149.RegularTerms.RegTerm.snd
end Lax709149.RegularTerms.RegTerm.snd

namespace Lax709149.RegularTerms.RegTerm.split
end Lax709149.RegularTerms.RegTerm.split

namespace Lax709149.RegularTerms.RegTerm.uncons
end Lax709149.RegularTerms.RegTerm.uncons

namespace Lax709149.RegularTerms

open Lax709149.Types

/-- The prefix products of a list: the `i`-th entry of the output is the product of
the first `i` entries of the input. -/
def prefixProd {M : Type} [Monoid M] (l : List M) : List M := (l.scanl (· * ·) 1).tail

end Lax709149.RegularTerms
end
