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

/-- A type is a finite alphabet if it has the form `1 + ⋯ + 1`. -/
def IsFinAlph (A : Ty) : Prop := ∃ n : ℕ, A = finAlph n

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

/-- A function is represented by a simple rational term if it is the function that the term
defines. -/
def IsSimpleFun {A : Ty} (f : ⟦A⟧ → List Bs) : Prop := ∃ t : SimpleTerm Bs A, t.den = f

end SimpleTerm

end Lax149335.SimpleRationalTerms
end

-- Lax149335.Terms
section
namespace Lax149335.Terms.Term.usesPref
end Lax149335.Terms.Term.usesPref

namespace Lax149335.Terms

open Lax149335.Types

/-- Auxiliary function used for the denotation of the group prefix multiplication: the `i`-th
group element of the output is the product of the first `i` group elements of the input. -/
def prefixMul {α G : Type} [Mul G] : G → List (α × G) → List (α × G)
  | _, [] => []
  | acc, (a, g) :: t => (a, acc * g) :: prefixMul (acc * g) t

/-- Auxiliary function used for the denotation of `split`: a list over `A + B` is split into a
maximal prefix of elements of `A`, followed by a list of blocks, each consisting of one
element of `B` and the following maximal run of elements of `A`. -/
def splitDen {α β : Type} : List (α ⊕ β) → List α × List (β × List α)
  | [] => ([], [])
  | .inl a :: t => let p := splitDen t; (a :: p.1, p.2)
  | .inr b :: t => let p := splitDen t; ([], (b, p.1) :: p.2)

/-- Auxiliary function used for the denotation of `snoc`. -/
def snocDen {α : Type} : Unit ⊕ (List α × α) → List α
  | .inl _ => []
  | .inr (l, a) => l ++ [a]

/-- Auxiliary function used for the denotation of `unsnoc`. -/
def unsnocDen {α : Type} (l : List α) : Unit ⊕ (List α × α) :=
  match l.reverse with
  | [] => .inl ()
  | a :: t => .inr (t.reverse, a)

/-- Auxiliary function used for the denotation of `shiftR`. -/
def shiftRDen {α β : Type} : List (α × β) → α → α × List (β × α)
  | [], a => (a, [])
  | (a₁, b₁) :: t, a => let p := shiftRDen t a; (a₁, (b₁, p.1) :: p.2)

/-- Auxiliary function used for the denotation of `shiftL`. -/
def shiftLDen {α β : Type} (a : α) : List (β × α) → List (α × β) × α
  | [] => ([], a)
  | (b₁, a₂) :: t => let p := shiftLDen a₂ t; ((a, b₁) :: p.1, p.2)

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

/-- The denotation `⟦f⟧` of a rational term: the function that it defines. -/
def den : {A B : Ty} → Term A B → ⟦A⟧ → ⟦B⟧
  | _, _, .comp f g, x => den g (den f x)
  | _, _, .prodF f g, x => (den f x.1, den g x.2)
  | _, _, .sumF f g, x =>
      match x with
      | .inl a => .inl (den f a)
      | .inr b => .inr (den g b)
  | _, _, .listF f, l => l.map (den f)
  | _, _, .id _, x => x
  | _, _, .inl _ _, x => .inl x
  | _, _, .inr _ _, x => .inr x
  | _, _, .codiag _, x => match x with | .inl a => a | .inr a => a
  | _, _, .fst _ _, x => x.1
  | _, _, .snd _ _, x => x.2
  | _, _, .unitR _, x => (x, ())
  | _, _, .unitL _, x => ((), x)
  | _, _, .assocL _ _ _, x => ((x.1, x.2.1), x.2.2)
  | _, _, .assocR _ _ _, x => (x.1.1, (x.1.2, x.2))
  | _, _, .distR _ _ _, x =>
      match x with
      | (a, .inl b) => .inl (a, b)
      | (a, .inr c) => .inr (a, c)
  | _, _, .distL _ _ _, x =>
      match x with
      | (.inl a, c) => .inl (a, c)
      | (.inr b, c) => .inr (b, c)
  | _, _, .cons _, x => match x with | .inl _ => [] | .inr (a, l) => a :: l
  | _, _, .uncons _, l => match l with | [] => .inl () | a :: t => .inr (a, t)
  | _, _, .snoc _, x => snocDen x
  | _, _, .unsnoc _, l => unsnocDen l
  | _, _, .concat _, l => l.flatten
  | _, _, .split _ _, l => splitDen l
  | _, _, .shiftR _ _, x => match x with | (l, a) => shiftRDen l a
  | _, _, .shiftL _ _, x => match x with | (a, l) => shiftLDen a l
  | _, _, .pref _ G, l => letI := G; prefixMul (1 : ⟦Ty.finAlph _⟧) l

end Term

end Lax149335.Terms
end

-- Lax149335.Simplification
section
namespace Lax149335.Simplification

open Lax149335.Types Lax149335.Terms Lax149335.SimpleRationalTerms

/-- **Theorem 2.9.** After precomposing with a rational term with surjective denotation, two
rational terms `N* → M*` are represented by simple rational terms. -/
axiom simplification_of_rational_terms {N M : Ty} (hN : Ty.IsFinAlph N)
    (hM : Ty.IsFinAlph M) (f g : Term N⋆ M⋆) :
    ∃ (C : Ty) (π : Term C N⋆), Function.Surjective π.den ∧
      SimpleTerm.IsSimpleFun (Bs := ⟦M⟧) (π ⨟ f).den ∧
      SimpleTerm.IsSimpleFun (Bs := ⟦M⟧) (π ⨟ g).den

end Lax149335.Simplification
end
