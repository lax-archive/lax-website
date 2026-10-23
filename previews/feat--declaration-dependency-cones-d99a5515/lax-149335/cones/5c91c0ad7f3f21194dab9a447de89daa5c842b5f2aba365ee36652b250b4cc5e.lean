-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Notation

-- Lax149335.Types
section
namespace Lax149335.Types.Ty.Sym
end Lax149335.Types.Ty.Sym

namespace Lax149335.Types.Ty.finAlph
end Lax149335.Types.Ty.finAlph

namespace Lax149335.Types.Ty.repr
end Lax149335.Types.Ty.repr

namespace Lax149335.Types.Ty.Sym.comma
end Lax149335.Types.Ty.Sym.comma

namespace Lax149335.Types.Ty.Sym.lbrack
end Lax149335.Types.Ty.Sym.lbrack

namespace Lax149335.Types.Ty.Sym.left
end Lax149335.Types.Ty.Sym.left

namespace Lax149335.Types.Ty.Sym.lpar
end Lax149335.Types.Ty.Sym.lpar

namespace Lax149335.Types.Ty.Sym.one
end Lax149335.Types.Ty.Sym.one

namespace Lax149335.Types.Ty.Sym.rbrack
end Lax149335.Types.Ty.Sym.rbrack

namespace Lax149335.Types.Ty.Sym.right
end Lax149335.Types.Ty.Sym.right

namespace Lax149335.Types.Ty.Sym.rpar
end Lax149335.Types.Ty.Sym.rpar

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

/-- A canonical element of every type. -/
def someElem : (A : Ty) → ⟦A⟧
  | .unit => ()
  | .prod A B => (someElem A, someElem B)
  | .sum A _ => .inl (someElem A)
  | .list _ => []

end Ty

end Lax149335.Types
end

-- Lax149335.SimpleRationalTerms
section
namespace Lax149335.SimpleRationalTerms
end Lax149335.SimpleRationalTerms

namespace Lax149335.SimpleRationalTerms.SimpleTerm
end Lax149335.SimpleRationalTerms.SimpleTerm

namespace Lax149335.SimpleRationalTerms.SimpleTerm.conc
end Lax149335.SimpleRationalTerms.SimpleTerm.conc

namespace Lax149335.SimpleRationalTerms.SimpleTerm.den
end Lax149335.SimpleRationalTerms.SimpleTerm.den

namespace Lax149335.SimpleRationalTerms.SimpleTerm.either
end Lax149335.SimpleRationalTerms.SimpleTerm.either

namespace Lax149335.SimpleRationalTerms.SimpleTerm.empty
end Lax149335.SimpleRationalTerms.SimpleTerm.empty

namespace Lax149335.SimpleRationalTerms.SimpleTerm.hom
end Lax149335.SimpleRationalTerms.SimpleTerm.hom

namespace Lax149335.SimpleRationalTerms.SimpleTerm.post
end Lax149335.SimpleRationalTerms.SimpleTerm.post

namespace Lax149335.SimpleRationalTerms.SimpleTerm.pre
end Lax149335.SimpleRationalTerms.SimpleTerm.pre
end

-- Lax149335.DecidableEquivalence
section
namespace Lax149335.DecidableEquivalence

open Lax149335.Types Lax149335.SimpleRationalTerms

/-- The test inputs `T(A)` of a type. -/
def testInputs : (A : Ty) → List ⟦A⟧
  | .unit => [()]
  | .sum A₁ A₂ => (testInputs A₁).map Sum.inl ++ (testInputs A₂).map Sum.inr
  | .prod A₁ A₂ =>
      (testInputs A₁).map (fun a => (a, Ty.someElem A₂)) ++
        (testInputs A₂).map (fun b => (Ty.someElem A₁, b))
  | .list A => [] :: (testInputs A).map (fun a => [a])

end Lax149335.DecidableEquivalence
end
