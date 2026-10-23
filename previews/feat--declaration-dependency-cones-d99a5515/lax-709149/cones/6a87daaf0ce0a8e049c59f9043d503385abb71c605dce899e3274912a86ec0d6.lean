-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

-- Lax709149.Types
section
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

/-- The alphabet with eight letters `(`, `)`, `[`, `]`, `,`, `1`, `L`, `R`. -/
inductive Sym8 : Type
  | lpar | rpar | lbrack | rbrack | comma | one | left | right
  deriving DecidableEq

/-- The entries of a list representation, separated by commas. -/
def joinSep : List (List Sym8) → List Sym8
  | [] => []
  | [x] => x
  | x :: xs => x ++ Sym8.comma :: joinSep xs

/-- The string representation of an element: `1` for the unit, `L a` and `R b` for
the co-product, `(a,b)` for a pair, `[a₁,…,aₙ]` for a list. -/
def Ty.repr : (t : Ty) → t.Elt → List Sym8
  | .one, _ => [Sym8.one]
  | .prod A B, x => Sym8.lpar :: (A.repr x.1 ++ Sym8.comma :: (B.repr x.2 ++ [Sym8.rpar]))
  | .sum A B, x => Sum.elim (fun a => Sym8.left :: A.repr a) (fun b => Sym8.right :: B.repr b) x
  | .list A, l => Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack])

end Lax709149.Types
end
