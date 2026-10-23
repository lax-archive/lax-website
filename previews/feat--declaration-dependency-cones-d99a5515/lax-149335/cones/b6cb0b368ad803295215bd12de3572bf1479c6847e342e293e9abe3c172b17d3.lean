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

end Ty

end Lax149335.Types
end

-- Lax149335.SimpleRationalTerms
section
namespace Lax149335.SimpleRationalTerms

open Lax149335.Types

/-- Simple rational terms `A → Bs*`. -/
inductive SimpleTerm (Bs : Type) : Ty → Type
  /-- The term `[] : 1 → Bs*` with empty output. -/
  | empty : SimpleTerm Bs Ty.unit
  /-- Co-pairing `⟨f₁, f₂⟩ : A₁ + A₂ → Bs*`. -/
  | either {A₁ A₂ : Ty} : SimpleTerm Bs A₁ → SimpleTerm Bs A₂ → SimpleTerm Bs (A₁ ⊕' A₂)
  /-- Concatenation `f₁ ⊙ f₂ : A₁ × A₂ → Bs*`. -/
  | conc {A₁ A₂ : Ty} : SimpleTerm Bs A₁ → SimpleTerm Bs A₂ → SimpleTerm Bs (A₁ ⊗ A₂)
  /-- Homomorphism `hom f : A* → Bs*`. -/
  | hom {A : Ty} : SimpleTerm Bs A → SimpleTerm Bs A⋆
  /-- Prepending a string constant, `w · f`. -/
  | pre {A : Ty} : List Bs → SimpleTerm Bs A → SimpleTerm Bs A
  /-- Appending a string constant, `f · w`. -/
  | post {A : Ty} : SimpleTerm Bs A → List Bs → SimpleTerm Bs A

namespace SimpleTerm

variable {Bs : Type}

/-- The function defined by a simple rational term. -/
def den : {A : Ty} → SimpleTerm Bs A → ⟦A⟧ → List Bs
  | _, .empty, _ => []
  | _, .either f _, .inl a => den f a
  | _, .either _ g, .inr b => den g b
  | _, .conc f g, (a, b) => den f a ++ den g b
  | _, .hom f, l => (l.map (den f)).flatten
  | _, .pre w f, a => w ++ den f a
  | _, .post f w, a => den f a ++ w

end SimpleTerm

end Lax149335.SimpleRationalTerms
end

-- Lax149335.SynchronisedLengths
section
namespace Lax149335.SynchronisedLengths.SimpleTerm.prodListTy
end Lax149335.SynchronisedLengths.SimpleTerm.prodListTy

namespace Lax149335.SynchronisedLengths.SimpleTerm.HomList.term
end Lax149335.SynchronisedLengths.SimpleTerm.HomList.term

namespace Lax149335.SynchronisedLengths

open Lax149335.Types Lax149335.SimpleRationalTerms

namespace SimpleTerm

variable {Bs : Type}

/-- A list of pairs `(fᵢ, wᵢ)` of a simple rational term `fᵢ : Aᵢ → Bs*` and a string `wᵢ`. -/
inductive HomList (Bs : Type) : List Ty → Type
  | nil : HomList Bs []
  | cons {A : Ty} {As : List Ty} : SimpleTerm Bs A → List Bs → HomList Bs As →
      HomList Bs (A :: As)

/-- Two lists of pairs whose terms `fᵢ` and `gᵢ` produce outputs of the same length on every
input. -/
def HomList.SameLengths : {As : List Ty} → HomList Bs As → HomList Bs As → Prop
  | _, .nil, .nil => True
  | _, .cons f _ F, .cons g _ G =>
      (∀ a, (f.den a).length = (g.den a).length) ∧ HomList.SameLengths F G

end SimpleTerm

open SimpleTerm

end Lax149335.SynchronisedLengths
end
