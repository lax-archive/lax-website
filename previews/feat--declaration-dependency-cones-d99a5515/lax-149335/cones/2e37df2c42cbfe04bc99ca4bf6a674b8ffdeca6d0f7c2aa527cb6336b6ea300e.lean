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

/-- **Corollary 2.8.** Two simple rational terms define the same function if and only if they
agree on all test inputs. -/
axiom decidable_equivalence {Bs : Type} {A : Ty} (f g : SimpleTerm Bs A) :
    f.den = g.den ↔ ∀ x ∈ testInputs A, f.den x = g.den x

end Lax149335.DecidableEquivalence
end
