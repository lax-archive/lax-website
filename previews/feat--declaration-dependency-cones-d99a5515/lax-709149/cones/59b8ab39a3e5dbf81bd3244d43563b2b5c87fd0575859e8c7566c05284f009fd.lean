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
namespace Lax709149.RegularTerms

open Lax709149.Types

/-- The prefix products of a list: the `i`-th entry of the output is the product of
the first `i` entries of the input. -/
def prefixProd {M : Type} [Monoid M] (l : List M) : List M := (l.scanl (· * ·) 1).tail

/-- Split: the input is cut at its entries from `B`; the output is the block of
entries from `A` before the first cut, and the cutting entries each with the block
that follows it. -/
def splitList {A B : Type} : List (A ⊕ B) → List A × List (B × List A)
  | [] => ([], [])
  | Sum.inl a :: l => ((splitList l).1.cons a, (splitList l).2)
  | Sum.inr b :: l => ([], (b, (splitList l).1) :: (splitList l).2)

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

/-- The function defined by a regular term. -/
def RegTerm.eval : {A B : Ty} → RegTerm A B → A.Elt → B.Elt
  | _, _, .id _ => fun x => x
  | _, _, .fst _ _ => fun x => x.1
  | _, _, .snd _ _ => fun x => x.2
  | _, _, .inl _ _ => fun x => Sum.inl x
  | _, _, .inr _ _ => fun x => Sum.inr x
  | _, _, .distr _ _ _ => fun x =>
      Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2
  | _, _, .cons _ => fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x
  | _, _, .uncons _ => fun l => match l with
      | [] => Sum.inl ()
      | a :: l' => Sum.inr (a, l')
  | _, _, .reverse _ => fun l => l.reverse
  | _, _, .concat _ => fun l => l.flatten
  | _, _, .split _ _ => fun l => splitList l
  | _, _, .pref _ grp _ => fun l => @prefixProd _ (@Group.toDivisionMonoid _ grp).toMonoid l
  | _, _, .comp s t => fun x => t.eval (s.eval x)
  | _, _, .pair s t => fun x => (s.eval x, t.eval x)
  | _, _, .copair s t => fun x => Sum.elim s.eval t.eval x
  | _, _, .map t => fun l => l.map t.eval

end Lax709149.RegularTerms
end
