-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Notation

-- Lax149335.Types
section
namespace Lax149335.Types.Ty.Sym
end Lax149335.Types.Ty.Sym

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

/-- The finite alphabet `1 + (1 + ⋯ + 1)` with `n + 1` letters. -/
def finAlph : ℕ → Ty
  | 0 => Ty.unit
  | (n + 1) => Ty.sum Ty.unit (finAlph n)

end Ty

end Lax149335.Types
end

-- Lax149335.Terms
section
namespace Lax149335.Terms.prefixMul
end Lax149335.Terms.prefixMul

namespace Lax149335.Terms.shiftLDen
end Lax149335.Terms.shiftLDen

namespace Lax149335.Terms.shiftRDen
end Lax149335.Terms.shiftRDen

namespace Lax149335.Terms.snocDen
end Lax149335.Terms.snocDen

namespace Lax149335.Terms.splitDen
end Lax149335.Terms.splitDen

namespace Lax149335.Terms.unsnocDen
end Lax149335.Terms.unsnocDen

namespace Lax149335.Terms.Term.den
end Lax149335.Terms.Term.den

namespace Lax149335.Terms.Term.usesPref
end Lax149335.Terms.Term.usesPref

namespace Lax149335.Terms

open Lax149335.Types

/-- **Definition 3.1 (Rational terms).** The expressions built from the atomic functions of
Figure 1 by composition and the functoriality combinators of products, co-products and
lists. -/
inductive Term : Ty → Ty → Type
  /-- Composition of functions. -/
  | comp {A B C : Ty} : Term A B → Term B C → Term A C
  /-- Functoriality of the product type constructor. -/
  | prodF {A₁ A₂ B₁ B₂ : Ty} : Term A₁ B₁ → Term A₂ B₂ → Term (A₁ ⊗ A₂) (B₁ ⊗ B₂)
  /-- Functoriality of the co-product type constructor. -/
  | sumF {A₁ A₂ B₁ B₂ : Ty} : Term A₁ B₁ → Term A₂ B₂ → Term (A₁ ⊕' A₂) (B₁ ⊕' B₂)
  /-- Functoriality of the list type constructor. -/
  | listF {A B : Ty} : Term A B → Term A⋆ B⋆
  /-- Atomic function 1: the identity. -/
  | id (A : Ty) : Term A A
  /-- Atomic function 2: the left co-projection. -/
  | inl (A B : Ty) : Term A (A ⊕' B)
  /-- Atomic function 2: the right co-projection. -/
  | inr (A B : Ty) : Term B (A ⊕' B)
  /-- Atomic function 3: the co-diagonal. -/
  | codiag (A : Ty) : Term (A ⊕' A) A
  /-- Atomic function 4: the first projection. -/
  | fst (A B : Ty) : Term (A ⊗ B) A
  /-- Atomic function 4: the second projection. -/
  | snd (A B : Ty) : Term (A ⊗ B) B
  /-- Atomic function 5: the right unit `(id, 1)`. -/
  | unitR (A : Ty) : Term A (A ⊗ Ty.unit)
  /-- Atomic function 5: the left unit `(1, id)`. -/
  | unitL (A : Ty) : Term A (Ty.unit ⊗ A)
  /-- Atomic function 5: left associativity of products. -/
  | assocL (A B C : Ty) : Term (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
  /-- Atomic function 5: right associativity of products. -/
  | assocR (A B C : Ty) : Term ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
  /-- Atomic function 6: distributivity on the right. -/
  | distR (A B C : Ty) : Term (A ⊗ (B ⊕' C)) ((A ⊗ B) ⊕' (A ⊗ C))
  /-- Atomic function 6: distributivity on the left. -/
  | distL (A B C : Ty) : Term ((A ⊕' B) ⊗ C) ((A ⊗ C) ⊕' (B ⊗ C))
  /-- Atomic function 7: the list constructor `cons`. -/
  | cons (A : Ty) : Term (Ty.unit ⊕' (A ⊗ A⋆)) A⋆
  /-- Atomic function 7: the list destructor `uncons`. -/
  | uncons (A : Ty) : Term A⋆ (Ty.unit ⊕' (A ⊗ A⋆))
  /-- Atomic function 7: the list constructor `snoc`. -/
  | snoc (A : Ty) : Term (Ty.unit ⊕' (A⋆ ⊗ A)) A⋆
  /-- Atomic function 7: the list destructor `unsnoc`. -/
  | unsnoc (A : Ty) : Term A⋆ (Ty.unit ⊕' (A⋆ ⊗ A))
  /-- Atomic function 8: concatenation of a list of lists. -/
  | concat (A : Ty) : Term A⋆⋆ A⋆
  /-- Atomic function 9: splitting a list over a co-product. -/
  | split (A B : Ty) : Term (A ⊕' B)⋆ (A⋆ ⊗ (B ⊗ A⋆)⋆)
  /-- Atomic function 10: shifting brackets to the right. -/
  | shiftR (A B : Ty) : Term ((A ⊗ B)⋆ ⊗ A) (A ⊗ (B ⊗ A)⋆)
  /-- Atomic function 10: shifting brackets to the left. -/
  | shiftL (A B : Ty) : Term (A ⊗ (B ⊗ A)⋆) ((A ⊗ B)⋆ ⊗ A)
  /-- Atomic function 11: prefix multiplication in a finite group whose underlying set is the
  finite alphabet `1 + ⋯ + 1`. -/
  | pref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
      Term ((A ⊗ Ty.finAlph n)⋆) ((A ⊗ Ty.finAlph n)⋆)

namespace Term

/-- Notation `f ⨟ g` for the composition of rational terms: first `f`, then `g`. -/
infixl:60 " ⨟ " => Term.comp

end Term

end Lax149335.Terms
end

-- Lax149335.DerivedTerms
section
namespace Lax149335.DerivedTerms.Term.TyF
end Lax149335.DerivedTerms.Term.TyF

namespace Lax149335.DerivedTerms.Term.TyF2
end Lax149335.DerivedTerms.Term.TyF2

namespace Lax149335.DerivedTerms.Term.caseR
end Lax149335.DerivedTerms.Term.caseR

namespace Lax149335.DerivedTerms.Term.constFin
end Lax149335.DerivedTerms.Term.constFin

namespace Lax149335.DerivedTerms.Term.TyF.app
end Lax149335.DerivedTerms.Term.TyF.app

namespace Lax149335.DerivedTerms.Term.TyF.list
end Lax149335.DerivedTerms.Term.TyF.list

namespace Lax149335.DerivedTerms.Term.TyF.param
end Lax149335.DerivedTerms.Term.TyF.param

namespace Lax149335.DerivedTerms.Term.TyF.pow
end Lax149335.DerivedTerms.Term.TyF.pow

namespace Lax149335.DerivedTerms.Term.TyF.prod
end Lax149335.DerivedTerms.Term.TyF.prod

namespace Lax149335.DerivedTerms.Term.TyF.sum
end Lax149335.DerivedTerms.Term.TyF.sum

namespace Lax149335.DerivedTerms.Term.TyF.unit
end Lax149335.DerivedTerms.Term.TyF.unit

namespace Lax149335.DerivedTerms.Term.TyF2.app
end Lax149335.DerivedTerms.Term.TyF2.app

namespace Lax149335.DerivedTerms.Term.TyF2.list
end Lax149335.DerivedTerms.Term.TyF2.list

namespace Lax149335.DerivedTerms.Term.TyF2.p1
end Lax149335.DerivedTerms.Term.TyF2.p1

namespace Lax149335.DerivedTerms.Term.TyF2.p2
end Lax149335.DerivedTerms.Term.TyF2.p2

namespace Lax149335.DerivedTerms.Term.TyF2.prod
end Lax149335.DerivedTerms.Term.TyF2.prod

namespace Lax149335.DerivedTerms.Term.TyF2.sum
end Lax149335.DerivedTerms.Term.TyF2.sum

namespace Lax149335.DerivedTerms.Term.TyF2.unit
end Lax149335.DerivedTerms.Term.TyF2.unit

namespace Lax149335.DerivedTerms

open Lax149335.Types Lax149335.Terms

namespace Term

open Lax149335.Terms.Term

/-- The empty list `[] : 1 → A*`, defined as `Left; cons`. -/
def nilT (A : Ty) : Term Ty.unit A⋆ := inl Ty.unit (A ⊗ A⋆) ⨟ cons A

/-- `prepend : A × A* → A*`, defined as `Right; cons`. -/
def prepend (A : Ty) : Term (A ⊗ A⋆) A⋆ := inr Ty.unit (A ⊗ A⋆) ⨟ cons A

/-- `pure : A → A*`, defined as `(id,1); id × []; prepend`. -/
def pureT (A : Ty) : Term A A⋆ :=
  unitR A ⨟ prodF (Term.id A) (nilT A) ⨟ prepend A

/-- `binconcat : A* × A* → A*`, defined as `(id × pure); prepend; concat`. -/
def binconcat (A : Ty) : Term (A⋆ ⊗ A⋆) A⋆ :=
  prodF (Term.id A⋆) (pureT A⋆) ⨟ prepend A⋆ ⨟ concat A

/-- Concatenation of two functions with list outputs, `f ⊙ g = (f × g); binconcat`. -/
def fdot {A₁ A₂ B : Ty} (f : Term A₁ B⋆) (g : Term A₂ B⋆) : Term (A₁ ⊗ A₂) B⋆ :=
  prodF f g ⨟ binconcat B

/-- Notation `f ⊙ g` for the concatenation of two terms with list outputs. -/
infixl:65 " ⊙ " => Term.fdot

/-- **Definition 5.1 (Value).** A value is a term of type `1 → A`. -/
abbrev Value (A : Ty) : Type := Term Ty.unit A

/-- Pairing a value on the right with an arbitrary term: `(f,v) = (id,1); (f × v)`. -/
def pairR {A B C : Ty} (f : Term A B) (v : Value C) : Term A (B ⊗ C) :=
  unitR A ⨟ prodF f v

end Term

end Lax149335.DerivedTerms
end
