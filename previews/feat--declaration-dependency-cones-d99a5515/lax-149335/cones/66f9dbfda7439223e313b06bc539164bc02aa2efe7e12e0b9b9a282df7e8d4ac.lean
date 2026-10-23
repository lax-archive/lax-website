-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Notation

-- Lax149335.Types
section
namespace Lax149335.Types.Ty.finAlph
end Lax149335.Types.Ty.finAlph

namespace Lax149335.Types

/-- Types: the unit type `1`, products `A × B`, co-products `A + B` and lists `A*`. -/
inductive Ty : Type
  | unit : Ty
  | prod : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  | list : Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Notation `A ⊗ B` for the product type. -/
infixl:70 " ⊗ " => Ty.prod

/-- Notation `A ⊕' B` for the co-product type. -/
infixl:65 " ⊕' " => Ty.sum

/-- Notation `A⋆` for the list type. -/
postfix:max "⋆" => Ty.list

/-- The set denoted by a type. -/
def den : Ty → Type
  | .unit => Unit
  | .prod A B => den A × den B
  | .sum A B => den A ⊕ den B
  | .list A => List (den A)

/-- Notation `⟦A⟧` for the set denoted by a type. -/
notation "⟦" A "⟧" => Ty.den A

/-- The eight-letter alphabet used to represent elements of types as strings. -/
inductive Sym : Type
  | lpar | rpar | lbrack | rbrack | comma | one | left | right
  deriving DecidableEq, Repr

/-- The string representing an element of a type: `1`, `Left a`, `Right b`, `(a,b)` and
`[a₁,…,aₙ]`. -/
def repr : (A : Ty) → ⟦A⟧ → List Sym
  | .unit, _ => [Sym.one]
  | .prod A B, (a, b) => Sym.lpar :: (repr A a ++ Sym.comma :: repr B b ++ [Sym.rpar])
  | .sum A _, .inl a => Sym.left :: repr A a
  | .sum _ B, .inr b => Sym.right :: repr B b
  | .list A, l =>
      Sym.lbrack :: ((l.map (repr A)).intersperse [Sym.comma]).flatten ++ [Sym.rbrack]

end Ty

end Lax149335.Types
end
