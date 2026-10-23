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
namespace Lax149335.SimpleRationalTerms.SimpleTerm.den
end Lax149335.SimpleRationalTerms.SimpleTerm.den

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

end SimpleTerm

end Lax149335.SimpleRationalTerms
end
