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

-- Lax149335.ConjugacyCompleteness
section
namespace Lax149335.ConjugacyCompleteness

open Lax149335.Types Lax149335.SimpleRationalTerms

namespace SimpleTerm

/-- The equivalence `≡` of simple rational terms from Theorem 2.6: the least relation closed
under (1) congruence, (2) concatenation monoidality, (3) constants and co-pairing, (4) case
splitting and (5) conjugacy. -/
inductive SEq {Bs : Type} : {A : Ty} → SimpleTerm Bs A → SimpleTerm Bs A → Prop
  -- (1) congruence, together with the equivalence relation rules
  | refl {A : Ty} (f : SimpleTerm Bs A) : SEq f f
  | symm {A : Ty} {f g : SimpleTerm Bs A} : SEq f g → SEq g f
  | trans {A : Ty} {f g h : SimpleTerm Bs A} : SEq f g → SEq g h → SEq f h
  | congr_either {A₁ A₂ : Ty} {f₁ g₁ : SimpleTerm Bs A₁} {f₂ g₂ : SimpleTerm Bs A₂} :
      SEq f₁ g₁ → SEq f₂ g₂ → SEq (.either f₁ f₂) (.either g₁ g₂)
  | congr_conc {A₁ A₂ : Ty} {f₁ g₁ : SimpleTerm Bs A₁} {f₂ g₂ : SimpleTerm Bs A₂} :
      SEq f₁ g₁ → SEq f₂ g₂ → SEq (.conc f₁ f₂) (.conc g₁ g₂)
  | congr_hom {A : Ty} {f g : SimpleTerm Bs A} : SEq f g → SEq (.hom f) (.hom g)
  | congr_pre {A : Ty} {f g : SimpleTerm Bs A} (w : List Bs) :
      SEq f g → SEq (.pre w f) (.pre w g)
  | congr_post {A : Ty} {f g : SimpleTerm Bs A} (w : List Bs) :
      SEq f g → SEq (.post f w) (.post g w)
  -- (2) concatenation monoidality
  | post_post {A : Ty} (f : SimpleTerm Bs A) (w v : List Bs) :
      SEq (.post (.post f w) v) (.post f (w ++ v))
  | pre_pre {A : Ty} (f : SimpleTerm Bs A) (w v : List Bs) :
      SEq (.pre w (.pre v f)) (.pre (w ++ v) f)
  | post_nil {A : Ty} (f : SimpleTerm Bs A) : SEq (.post f []) f
  | pre_nil {A : Ty} (f : SimpleTerm Bs A) : SEq (.pre [] f) f
  | pre_post {A : Ty} (f : SimpleTerm Bs A) (w v : List Bs) :
      SEq (.post (.pre w f) v) (.pre w (.post f v))
  | conc_shift {A₁ A₂ : Ty} (f : SimpleTerm Bs A₁) (g : SimpleTerm Bs A₂) (w : List Bs) :
      SEq (.conc (.post f w) g) (.conc f (.pre w g))
  | pre_conc {A₁ A₂ : Ty} (w : List Bs) (f₁ : SimpleTerm Bs A₁) (f₂ : SimpleTerm Bs A₂) :
      SEq (.pre w (.conc f₁ f₂)) (.conc (.pre w f₁) f₂)
  | post_conc {A₁ A₂ : Ty} (w : List Bs) (f₁ : SimpleTerm Bs A₁) (f₂ : SimpleTerm Bs A₂) :
      SEq (.post (.conc f₁ f₂) w) (.conc f₁ (.post f₂ w))
  | move_empty (w : List Bs) :
      SEq (.post (.empty : SimpleTerm Bs Ty.unit) w) (.pre w .empty)
  -- (3) constants and copairing
  | pre_either {A₁ A₂ : Ty} (w : List Bs) (f₁ : SimpleTerm Bs A₁) (f₂ : SimpleTerm Bs A₂) :
      SEq (.pre w (.either f₁ f₂)) (.either (.pre w f₁) (.pre w f₂))
  | post_either {A₁ A₂ : Ty} (w : List Bs) (f₁ : SimpleTerm Bs A₁) (f₂ : SimpleTerm Bs A₂) :
      SEq (.post (.either f₁ f₂) w) (.either (.post f₁ w) (.post f₂ w))
  -- (4) case splitting
  | case_left {A₁ A₂ A : Ty} {f₁ g₁ : SimpleTerm Bs A₁} {f₂ g₂ : SimpleTerm Bs A₂}
      {h : SimpleTerm Bs A} :
      SEq (.either (.conc f₁ h) (.conc f₂ h)) (.either (.conc g₁ h) (.conc g₂ h)) →
      SEq (.conc (.either f₁ f₂) h) (.conc (.either g₁ g₂) h)
  | case_right {A₁ A₂ A : Ty} {f₁ g₁ : SimpleTerm Bs A₁} {f₂ g₂ : SimpleTerm Bs A₂}
      {h : SimpleTerm Bs A} :
      SEq (.either (.conc h f₁) (.conc h f₂)) (.either (.conc h g₁) (.conc h g₂)) →
      SEq (.conc h (.either f₁ f₂)) (.conc h (.either g₁ g₂))
  -- (5) conjugacy
  | conjugacy {A : Ty} {f g : SimpleTerm Bs A} (w : List Bs) :
      SEq (.post f w) (.pre w g) → SEq (.post (.hom f) w) (.pre w (.hom g))

/-- Notation `f ≃ₛ g` for the equivalence of simple rational terms. -/
infix:50 " ≃ₛ " => SEq

end SimpleTerm

end Lax149335.ConjugacyCompleteness
end
