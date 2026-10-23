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
namespace Lax149335.DerivedTerms.Term.TyF.pow
end Lax149335.DerivedTerms.Term.TyF.pow

namespace Lax149335.DerivedTerms

open Lax149335.Types Lax149335.Terms

namespace Term

open Lax149335.Terms.Term

/-- The unique function into the unit type, `A → 1`. -/
def toUnit (A : Ty) : Term A Ty.unit := unitL A ⨟ fst Ty.unit A

/-- Co-pairing, a derived combinator: `either f₁ f₂ = (f₁ + f₂); codiag`. -/
def either {A₁ A₂ B : Ty} (f₁ : Term A₁ B) (f₂ : Term A₂ B) : Term (A₁ ⊕' A₂) B :=
  sumF f₁ f₂ ⨟ codiag B

/-- The empty list `[] : 1 → A*`, defined as `Left; cons`. -/
def nilT (A : Ty) : Term Ty.unit A⋆ := inl Ty.unit (A ⊗ A⋆) ⨟ cons A

/-- `prepend : A × A* → A*`, defined as `Right; cons`. -/
def prepend (A : Ty) : Term (A ⊗ A⋆) A⋆ := inr Ty.unit (A ⊗ A⋆) ⨟ cons A

/-- `append : A* × A → A*`, defined as `Right; snoc`. -/
def append (A : Ty) : Term (A⋆ ⊗ A) A⋆ := inr Ty.unit (A⋆ ⊗ A) ⨟ snoc A

/-- `pure : A → A*`, defined as `(id,1); id × []; prepend`. -/
def pureT (A : Ty) : Term A A⋆ :=
  unitR A ⨟ prodF (Term.id A) (nilT A) ⨟ prepend A

/-- `binconcat : A* × A* → A*`, defined as `(id × pure); prepend; concat`. -/
def binconcat (A : Ty) : Term (A⋆ ⊗ A⋆) A⋆ :=
  prodF (Term.id A⋆) (pureT A⋆) ⨟ prepend A⋆ ⨟ concat A

/-- The homomorphism combinator `hom f = f*; concat`. -/
def homT {A B : Ty} (f : Term A B⋆) : Term A⋆ B⋆ := listF f ⨟ concat B

/-- Concatenation of two functions with list outputs, `f ⊙ g = (f × g); binconcat`. -/
def fdot {A₁ A₂ B : Ty} (f : Term A₁ B⋆) (g : Term A₂ B⋆) : Term (A₁ ⊗ A₂) B⋆ :=
  prodF f g ⨟ binconcat B

/-- Notation `f ⊙ g` for the concatenation of two terms with list outputs. -/
infixl:65 " ⊙ " => Term.fdot

/-- The inverse of distributivity on the right,
`undistR = either (id × Left) (id × Right)`. -/
def undistR (A B C : Ty) : Term ((A ⊗ B) ⊕' (A ⊗ C)) (A ⊗ (B ⊕' C)) :=
  either (prodF (Term.id A) (inl B C)) (prodF (Term.id A) (inr B C))

/-- The inverse of distributivity on the left. -/
def undistL (A B C : Ty) : Term ((A ⊗ C) ⊕' (B ⊗ C)) ((A ⊕' B) ⊗ C) :=
  either (prodF (inl A B) (Term.id C)) (prodF (inr A B) (Term.id C))

/-- **Definition 5.1 (Value).** A value is a term of type `1 → A`. -/
abbrev Value (A : Ty) : Type := Term Ty.unit A

/-- Pairing a value on the left with an arbitrary term: `(v,f) = (1,id); (v × f)`. -/
def pairL {A B C : Ty} (v : Value C) (f : Term A B) : Term A (C ⊗ B) :=
  unitL A ⨟ prodF v f

/-- Pairing a value on the right with an arbitrary term: `(f,v) = (id,1); (f × v)`. -/
def pairR {A B C : Ty} (f : Term A B) (v : Value C) : Term A (B ⊗ C) :=
  unitR A ⨟ prodF f v

/-- The *head term for `w`*: the first element of a list, or the value `w` if the list is
empty. -/
def headT {A : Ty} (w : Value A) : Term A⋆ A :=
  uncons A ⨟ either w (fst A A⋆)

/-- Type constructors with one parameter, used to define concatenation maps. -/
inductive TyF : Type
  /-- The parameter itself. -/
  | param : TyF
  /-- The unit type. -/
  | unit : TyF
  /-- Product of two type constructors. -/
  | prod : TyF → TyF → TyF
  /-- Co-product of two type constructors. -/
  | sum : TyF → TyF → TyF
  /-- List of a type constructor. -/
  | list : TyF → TyF

/-- The type `F(A)` obtained by substituting the type `A` for the parameter of `F`. -/
def TyF.app : TyF → Ty → Ty
  | .param, A => A
  | .unit, _ => Ty.unit
  | .prod F G, A => (F.app A) ⊗ (G.app A)
  | .sum F G, A => (F.app A) ⊕' (G.app A)
  | .list F, A => (F.app A)⋆

/-- **Concatenation maps** (Section 5.1): the term `F(A) ↣ A*` that concatenates all the
elements of the input into a single list, defined by induction on `F`. -/
def TyF.concatMap : (F : TyF) → (A : Ty) → Term (F.app A) A⋆
  | .param, A => pureT A
  | .unit, A => nilT A
  | .prod F G, A => (F.concatMap A) ⊙ (G.concatMap A)
  | .sum F G, A => either (F.concatMap A) (G.concatMap A)
  | .list F, A => homT (F.concatMap A)

/-- Type constructors with two parameters, used for the concatenation maps with values in
`(A + B)*` that occur in Axiom 15 and in the definition of `unsplit`. -/
inductive TyF2 : Type
  /-- The first parameter. -/
  | p1 : TyF2
  /-- The second parameter. -/
  | p2 : TyF2
  /-- The unit type. -/
  | unit : TyF2
  /-- Product of two type constructors. -/
  | prod : TyF2 → TyF2 → TyF2
  /-- Co-product of two type constructors. -/
  | sum : TyF2 → TyF2 → TyF2
  /-- List of a type constructor. -/
  | list : TyF2 → TyF2

/-- The type `F(A,B)`. -/
def TyF2.app : TyF2 → Ty → Ty → Ty
  | .p1, A, _ => A
  | .p2, _, B => B
  | .unit, _, _ => Ty.unit
  | .prod F G, A, B => (F.app A B) ⊗ (G.app A B)
  | .sum F G, A, B => (F.app A B) ⊕' (G.app A B)
  | .list F, A, B => (F.app A B)⋆

/-- The concatenation map `F(A,B) ↣ (A+B)*`, which injects the elements of `A` and of `B`
into the co-product `A + B` and concatenates all of them. -/
def TyF2.concatMap : (F : TyF2) → (A B : Ty) → Term (F.app A B) (A ⊕' B)⋆
  | .p1, A, B => inl A B ⨟ pureT (A ⊕' B)
  | .p2, A, B => inr A B ⨟ pureT (A ⊕' B)
  | .unit, A, B => nilT (A ⊕' B)
  | .prod F G, A, B => (F.concatMap A B) ⊙ (G.concatMap A B)
  | .sum F G, A, B => either (F.concatMap A B) (G.concatMap A B)
  | .list F, A, B => homT (F.concatMap A B)

/-- The inverse of `split`: it injects `A` and `B` into the co-product `A + B` and then
concatenates all resulting lists. -/
def unsplit (A B : Ty) : Term (A⋆ ⊗ (B ⊗ A⋆)⋆) (A ⊕' B)⋆ :=
  TyF2.concatMap (.prod (.list .p1) (.list (.prod .p2 (.list .p1)))) A B

/-- The value `1 → 1 + ⋯ + 1` that picks out a given letter of a finite alphabet. -/
def constFin : {n : ℕ} → ⟦Ty.finAlph n⟧ → Value (Ty.finAlph n)
  | 0, _ => Term.id Ty.unit
  | (_ + 1), .inl _ => inl Ty.unit _
  | (_ + 1), .inr g => constFin g ⨟ inr Ty.unit _

/-- Case analysis on a letter of a finite alphabet that appears as the right component of a
product; it is derived using distributivity and co-pairing. -/
def caseR : {n : ℕ} → {A B : Ty} → (⟦Ty.finAlph n⟧ → Term A B) → Term (A ⊗ Ty.finAlph n) B
  | 0, A, _, t => fst A Ty.unit ⨟ t ()
  | (n + 1), A, _, t =>
      distR A Ty.unit (Ty.finAlph n) ⨟
        either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g => t (.inr g)))

/-- Case analysis on a letter of a finite alphabet that appears as the left component of a
product. -/
def caseL : {n : ℕ} → {A B : Ty} → (⟦Ty.finAlph n⟧ → Term A B) → Term (Ty.finAlph n ⊗ A) B
  | 0, A, _, t => snd Ty.unit A ⨟ t ()
  | (n + 1), A, _, t =>
      distL Ty.unit (Ty.finAlph n) A ⨟
        either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g => t (.inr g)))

/-- The term `(a,g) ↦ (g,(a,g))`, admissible because the group is a finite alphabet. -/
def grepeat (A : Ty) (n : ℕ) : Term (A ⊗ Ty.finAlph n) (Ty.finAlph n ⊗ (A ⊗ Ty.finAlph n)) :=
  caseR (fun g => pairL (constFin g) (pairR (Term.id A) (constFin g)))

/-- The term `(h,(g,a)) ↦ (a, h⁻¹ · g)`, admissible because the group is a finite
alphabet. -/
def gdiv (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term (Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A)) (A ⊗ Ty.finAlph n) :=
  caseL (fun h => caseL (fun g => pairR (Term.id A) (constFin (letI := G; h⁻¹ * g))))

/-- The unprefixing operation, the inverse of the group prefix multiplication:
`[(a₁,g₁),…,(aₙ,gₙ)] ↦ [(a₁,g₀⁻¹g₁),(a₂,g₁⁻¹g₂),…,(aₙ,gₙ₋₁⁻¹gₙ)]`, where `g₀` is the group
identity. -/
def unpref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term ((A ⊗ Ty.finAlph n)⋆) ((A ⊗ Ty.finAlph n)⋆) :=
  listF (grepeat A n) ⨟
    listF (assocL (Ty.finAlph n) A (Ty.finAlph n)) ⨟
      pairL (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) (Term.id _) ⨟
        shiftL (Ty.finAlph n) (Ty.finAlph n ⊗ A) ⨟
          fst _ _ ⨟ listF (gdiv A G)

end Term

end Lax149335.DerivedTerms
end

-- Lax149335.EquationalTheory
section
namespace Lax149335.EquationalTheory

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms

namespace Term

open Lax149335.Terms.Term Lax149335.DerivedTerms.Term

/-- The cyclic group `ℤ₂` of order two, with the two letter alphabet `2 = 1 + 1` as its
underlying set: the group identity is the first letter `Left`, and the second letter `Right`
is the generator. -/
def cyclicTwo : Group ⟦Ty.finAlph 1⟧ where
  mul x y := match x, y with
    | .inl _, y => y
    | x, .inl _ => x
    | .inr _, .inr _ => .inl ()
  one := .inl ()
  inv x := x
  mul_assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  one_mul := by intro x; cases x <;> rfl
  mul_one := by intro x; cases x <;> rfl
  inv_mul_cancel := by intro x; cases x <;> rfl

/-- **Step 3 of the bundle term**, for a single element: `distR ; either (fst ; Right)
(fst ; Left) : A × 2 → A + A`.  An element annotated with the generator `Right` goes to the
left copy of `A`, and an element annotated with the identity `Left` goes to the right
copy. -/
def bundleTag (A : Ty) : Term (A ⊗ Ty.finAlph 1) (A ⊕' A) :=
  distR A Ty.unit (Ty.finAlph 0) ⨟ either (fst A Ty.unit ⨟ inr A A) (fst A Ty.unit ⨟ inl A A)

/-- **Definition H.5 (the bundle term)** `A* → (A × A)* × (1 + A)`, for a type `A` and a value
`w : 1 → A`:

`((id,1) ; (id × Right))* ; pref_{ℤ₂} ; (distR ; either (fst ; Right) (fst ; Left))* ;
split ; shiftL ; ((head_w × id)* × (uncons ; (id + fst)))`.

The window axiom (Axiom 16) says that, for `A = 2*` and `w = []`, it is a one-sided inverse
of the concatenation map `(A × A)* × (1 + A) ↣ A*`. -/
def bundle (A : Ty) (w : Value A) : Term A⋆ ((A ⊗ A)⋆ ⊗ (Ty.unit ⊕' A)) :=
  listF (unitR A ⨟ prodF (Term.id A) (inr Ty.unit (Ty.finAlph 0))) ⨟
    pref A cyclicTwo ⨟
    listF (bundleTag A) ⨟
    split A A ⨟
    shiftL A⋆ A ⨟
    prodF (listF (prodF (headT w) (Term.id A))) (uncons A ⨟ sumF (Term.id Ty.unit) (fst A A⋆))

/-- The type constructor `A ↦ (A × A)* × (1 + A)` of the window axiom. -/
def TyF.window : TyF := .prod (.list (.prod .param .param)) (.sum .unit .param)

end Term

open Lax149335.Terms.Term Lax149335.DerivedTerms.Term

/-- Provable equality of rational terms: the least equivalence relation containing
Axioms 1-16 of Section 4 and stable under the combinators of the system. -/
inductive PEq : {A B : Ty} → Term A B → Term A B → Prop
  -- rules of equational reasoning: `≡` is an equivalence relation, stable under the
  -- four combinators of the system
  | refl {A B : Ty} (f : Term A B) : PEq f f
  | symm {A B : Ty} {f g : Term A B} : PEq f g → PEq g f
  | trans {A B : Ty} {f g h : Term A B} : PEq f g → PEq g h → PEq f h
  | congr_comp {A B C : Ty} {f f' : Term A B} {g g' : Term B C} :
      PEq f f' → PEq g g' → PEq (f ⨟ g) (f' ⨟ g')
  | congr_prodF {A₁ A₂ B₁ B₂ : Ty} {f f' : Term A₁ B₁} {g g' : Term A₂ B₂} :
      PEq f f' → PEq g g' → PEq (prodF f g) (prodF f' g')
  | congr_sumF {A₁ A₂ B₁ B₂ : Ty} {f f' : Term A₁ B₁} {g g' : Term A₂ B₂} :
      PEq f f' → PEq g g' → PEq (sumF f g) (sumF f' g')
  | congr_listF {A B : Ty} {f f' : Term A B} : PEq f f' → PEq (listF f) (listF f')
  -- ## Axiom 1 (category axioms)
  | comp_assoc {A B C D : Ty} (f : Term A B) (g : Term B C) (h : Term C D) :
      PEq ((f ⨟ g) ⨟ h) (f ⨟ (g ⨟ h))
  | id_comp {A B : Ty} (f : Term A B) : PEq (Term.id A ⨟ f) f
  | comp_id {A B : Ty} (f : Term A B) : PEq (f ⨟ Term.id B) f
  -- ## Axiom 2 (functoriality), first part: the functors preserve the identity
  | prod_id (A B : Ty) : PEq (prodF (Term.id A) (Term.id B)) (Term.id (A ⊗ B))
  | sum_id (A B : Ty) : PEq (sumF (Term.id A) (Term.id B)) (Term.id (A ⊕' B))
  | list_id (A : Ty) : PEq (listF (Term.id A)) (Term.id A⋆)
  -- ## Axiom 2 (functoriality), second part: the functors preserve composition
  | prod_comp {A₁ A₂ B₁ B₂ C₁ C₂ : Ty} (f₁ : Term A₁ B₁) (f₂ : Term A₂ B₂)
      (g₁ : Term B₁ C₁) (g₂ : Term B₂ C₂) :
      PEq (prodF f₁ f₂ ⨟ prodF g₁ g₂) (prodF (f₁ ⨟ g₁) (f₂ ⨟ g₂))
  | sum_comp {A₁ A₂ B₁ B₂ C₁ C₂ : Ty} (f₁ : Term A₁ B₁) (f₂ : Term A₂ B₂)
      (g₁ : Term B₁ C₁) (g₂ : Term B₂ C₂) :
      PEq (sumF f₁ f₂ ⨟ sumF g₁ g₂) (sumF (f₁ ⨟ g₁) (f₂ ⨟ g₂))
  | list_comp {A B C : Ty} (f : Term A B) (g : Term B C) :
      PEq (listF f ⨟ listF g) (listF (f ⨟ g))
  -- ## Axiom 3 (each atomic function is a natural transformation)
  | nat_inl {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (inl A B ⨟ sumF f g) (f ⨟ inl A' B')
  | nat_inr {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (inr A B ⨟ sumF f g) (g ⨟ inr A' B')
  | nat_codiag {A A' : Ty} (f : Term A A') :
      PEq (sumF f f ⨟ codiag A') (codiag A ⨟ f)
  | nat_fst {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (prodF f g ⨟ fst A' B') (fst A B ⨟ f)
  | nat_snd {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (prodF f g ⨟ snd A' B') (snd A B ⨟ g)
  | nat_unitR {A A' : Ty} (f : Term A A') :
      PEq (f ⨟ unitR A') (unitR A ⨟ prodF f (Term.id Ty.unit))
  | nat_unitL {A A' : Ty} (f : Term A A') :
      PEq (f ⨟ unitL A') (unitL A ⨟ prodF (Term.id Ty.unit) f)
  | nat_assocL {A A' B B' C C' : Ty} (f₁ : Term A A') (f₂ : Term B B') (f₃ : Term C C') :
      PEq (prodF f₁ (prodF f₂ f₃) ⨟ assocL A' B' C') (assocL A B C ⨟ prodF (prodF f₁ f₂) f₃)
  | nat_assocR {A A' B B' C C' : Ty} (f₁ : Term A A') (f₂ : Term B B') (f₃ : Term C C') :
      PEq (prodF (prodF f₁ f₂) f₃ ⨟ assocR A' B' C') (assocR A B C ⨟ prodF f₁ (prodF f₂ f₃))
  | nat_distR {A A' B B' C C' : Ty} (f : Term A A') (g : Term B B') (h : Term C C') :
      PEq (prodF f (sumF g h) ⨟ distR A' B' C') (distR A B C ⨟ sumF (prodF f g) (prodF f h))
  | nat_distL {A A' B B' C C' : Ty} (f : Term A A') (g : Term B B') (h : Term C C') :
      PEq (prodF (sumF f g) h ⨟ distL A' B' C') (distL A B C ⨟ sumF (prodF f h) (prodF g h))
  | nat_cons {A B : Ty} (f : Term A B) :
      PEq (sumF (Term.id Ty.unit) (prodF f (listF f)) ⨟ cons B) (cons A ⨟ listF f)
  | nat_uncons {A B : Ty} (f : Term A B) :
      PEq (listF f ⨟ uncons B) (uncons A ⨟ sumF (Term.id Ty.unit) (prodF f (listF f)))
  | nat_snoc {A B : Ty} (f : Term A B) :
      PEq (sumF (Term.id Ty.unit) (prodF (listF f) f) ⨟ snoc B) (snoc A ⨟ listF f)
  | nat_unsnoc {A B : Ty} (f : Term A B) :
      PEq (listF f ⨟ unsnoc B) (unsnoc A ⨟ sumF (Term.id Ty.unit) (prodF (listF f) f))
  | nat_concat {A B : Ty} (f : Term A B) :
      PEq (listF (listF f) ⨟ concat B) (concat A ⨟ listF f)
  | nat_split {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (listF (sumF f g) ⨟ split A' B')
        (split A B ⨟ prodF (listF f) (listF (prodF g (listF f))))
  | nat_shiftR {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (prodF (listF (prodF f g)) f ⨟ shiftR A' B')
        (shiftR A B ⨟ prodF f (listF (prodF g f)))
  | nat_shiftL {A A' B B' : Ty} (f : Term A A') (g : Term B B') :
      PEq (prodF f (listF (prodF g f)) ⨟ shiftL A' B')
        (shiftL A B ⨟ prodF (listF (prodF f g)) f)
  -- (Naturality of the group prefix multiplication need not be postulated: it is derivable,
  -- see footnote 5 of the paper.)
  -- ## Axiom 4 (ten pairs of mutually inverse functions)
  | unitR_fst (A : Ty) : PEq (unitR A ⨟ fst A Ty.unit) (Term.id A)
  | fst_unitR (A : Ty) : PEq (fst A Ty.unit ⨟ unitR A) (Term.id (A ⊗ Ty.unit))
  | unitL_snd (A : Ty) : PEq (unitL A ⨟ snd Ty.unit A) (Term.id A)
  | snd_unitL (A : Ty) : PEq (snd Ty.unit A ⨟ unitL A) (Term.id (Ty.unit ⊗ A))
  | assocL_assocR (A B C : Ty) :
      PEq (assocL A B C ⨟ assocR A B C) (Term.id (A ⊗ (B ⊗ C)))
  | assocR_assocL (A B C : Ty) :
      PEq (assocR A B C ⨟ assocL A B C) (Term.id ((A ⊗ B) ⊗ C))
  | distL_undistL (A B C : Ty) :
      PEq (distL A B C ⨟ undistL A B C) (Term.id ((A ⊕' B) ⊗ C))
  | undistL_distL (A B C : Ty) :
      PEq (undistL A B C ⨟ distL A B C) (Term.id ((A ⊗ C) ⊕' (B ⊗ C)))
  | distR_undistR (A B C : Ty) :
      PEq (distR A B C ⨟ undistR A B C) (Term.id (A ⊗ (B ⊕' C)))
  | undistR_distR (A B C : Ty) :
      PEq (undistR A B C ⨟ distR A B C) (Term.id ((A ⊗ B) ⊕' (A ⊗ C)))
  | cons_uncons (A : Ty) : PEq (cons A ⨟ uncons A) (Term.id (Ty.unit ⊕' (A ⊗ A⋆)))
  | uncons_cons (A : Ty) : PEq (uncons A ⨟ cons A) (Term.id A⋆)
  | snoc_unsnoc (A : Ty) : PEq (snoc A ⨟ unsnoc A) (Term.id (Ty.unit ⊕' (A⋆ ⊗ A)))
  | unsnoc_snoc (A : Ty) : PEq (unsnoc A ⨟ snoc A) (Term.id A⋆)
  | split_unsplit (A B : Ty) : PEq (split A B ⨟ unsplit A B) (Term.id (A ⊕' B)⋆)
  | unsplit_split (A B : Ty) : PEq (unsplit A B ⨟ split A B) (Term.id (A⋆ ⊗ (B ⊗ A⋆)⋆))
  | pref_unpref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
      PEq (pref A G ⨟ unpref A G) (Term.id ((A ⊗ Ty.finAlph n)⋆))
  | unpref_pref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
      PEq (unpref A G ⨟ pref A G) (Term.id ((A ⊗ Ty.finAlph n)⋆))
  | shiftL_shiftR (A B : Ty) : PEq (shiftL A B ⨟ shiftR A B) (Term.id (A ⊗ (B ⊗ A)⋆))
  | shiftR_shiftL (A B : Ty) : PEq (shiftR A B ⨟ shiftL A B) (Term.id ((A ⊗ B)⋆ ⊗ A))
  -- ## Axiom 5 (the unit type is terminal)
  | unit_unique {A : Ty} (f g : Term A Ty.unit) : PEq f g
  -- ## Axiom 6 (the co-diagonal)
  | inl_codiag (A : Ty) : PEq (inl A A ⨟ codiag A) (Term.id A)
  | inr_codiag (A : Ty) : PEq (inr A A ⨟ codiag A) (Term.id A)
  | sum_inl_inr_codiag (A B : Ty) :
      PEq (sumF (inl A B) (inr A B) ⨟ codiag (A ⊕' B)) (Term.id (A ⊕' B))
  -- ## Axiom 7 (Mac Lane's pentagon)
  | pentagon (A B C D : Ty) :
      PEq (prodF (Term.id A) (assocL B C D) ⨟ assocL A (B ⊗ C) D ⨟
              prodF (assocL A B C) (Term.id D))
        (assocL A B (C ⊗ D) ⨟ assocL (A ⊗ B) C D)
  -- ## Axiom 8 (Mac Lane's triangle)
  | triangle (A C : Ty) :
      PEq (assocL A Ty.unit C ⨟ prodF (fst A Ty.unit) (Term.id C))
        (prodF (Term.id A) (snd Ty.unit C))
  -- ## Axiom 9 (`snoc`-based notation agrees with `cons`-based notation)
  | inl_snoc_cons (A : Ty) :
      PEq (inl Ty.unit (A⋆ ⊗ A) ⨟ snoc A) (inl Ty.unit (A ⊗ A⋆) ⨟ cons A)
  | append_nil_prepend_nil (A : Ty) :
      PEq (unitL A ⨟ prodF (nilT A) (Term.id A) ⨟ append A)
        (unitR A ⨟ prodF (Term.id A) (nilT A) ⨟ prepend A)
  | append_concat_prepend_concat (A : Ty) :
      PEq (prodF (pureT A⋆) (Term.id A⋆) ⨟ append A⋆ ⨟ concat A)
        (prodF (Term.id A⋆) (pureT A⋆) ⨟ prepend A⋆ ⨟ concat A)
  -- ## Axiom 10 (`A*` is a monoid)
  | binconcat_assoc (A : Ty) :
      PEq (prodF (binconcat A) (Term.id A⋆) ⨟ binconcat A)
        (assocR A⋆ A⋆ A⋆ ⨟ prodF (Term.id A⋆) (binconcat A) ⨟ binconcat A)
  | binconcat_unitR (A : Ty) :
      PEq (unitR A⋆ ⨟ prodF (Term.id A⋆) (nilT A) ⨟ binconcat A) (Term.id A⋆)
  | binconcat_unitL (A : Ty) :
      PEq (unitL A⋆ ⨟ prodF (nilT A) (Term.id A⋆) ⨟ binconcat A) (Term.id A⋆)
  -- ## Axiom 11 (`concat` is a monoid homomorphism)
  | nil_concat (A : Ty) : PEq (nilT A⋆ ⨟ concat A) (nilT A)
  | binconcat_concat (A : Ty) :
      PEq (binconcat A⋆ ⨟ concat A) (prodF (concat A) (concat A) ⨟ binconcat A)
  -- ## Axiom 12 (`A*` is a monad)
  | concat_concat (A : Ty) : PEq (listF (concat A) ⨟ concat A) (concat A⋆ ⨟ concat A)
  | pure_concat (A : Ty) : PEq (pureT A⋆ ⨟ concat A) (Term.id A⋆)
  | listF_pure_concat (A : Ty) : PEq (listF (pureT A) ⨟ concat A) (Term.id A⋆)
  -- ## Axiom 13 (the inductive structure in terms of the monoid structure)
  | prepend_def (A : Ty) :
      PEq (prepend A) (prodF (pureT A) (Term.id A⋆) ⨟ binconcat A)
  | append_def (A : Ty) :
      PEq (append A) (prodF (Term.id A⋆) (pureT A) ⨟ binconcat A)
  -- ## Axiom 14 (concatenating a list of empty lists)
  | nil_map_concat (A : Ty) :
      PEq (listF (nilT A) ⨟ concat A) (toUnit Ty.unit⋆ ⨟ nilT A)
  -- ## Axiom 15 (`shiftR` does not change the content of the list)
  | shiftR_content (A B : Ty) :
      PEq (shiftR A B ⨟ TyF2.concatMap (.prod .p1 (.list (.prod .p2 .p1))) A B)
        (TyF2.concatMap (.prod (.list (.prod .p1 .p2)) .p1) A B)
  -- ## Axiom 16 (the window axiom: the bundle term undoes the concatenation map of bundles
  -- of size two over binary strings)
  --
  -- The bundle term `bundle_{2*} : (2*)* → (2* × 2*)* × (1 + 2*)` of Definition H.5,
  -- formalised as `Term.bundle` with the value `w = []`, splits a list into bundles
  -- of two consecutive entries followed by a remainder of at most one entry.  The axiom says
  -- that this splitting is undone by the concatenation map
  --
  --   `(2* × 2*)* × (1 + 2*) ↣ (2*)*`,
  --
  -- i.e. that `bundle ; concat ≡ id`.
  | window :
      PEq (Term.bundle ((Ty.finAlph 1)⋆) (nilT (Ty.finAlph 1)) ⨟
            TyF.concatMap Term.TyF.window ((Ty.finAlph 1)⋆))
        (Term.id (((Ty.finAlph 1)⋆)⋆))

/-- Notation `f ≡ₜ g` for provable equivalence of rational terms. -/
infix:50 " ≡ₜ " => PEq

end Lax149335.EquationalTheory
end

-- Lax149335.InjectiveSurjectiveTerms
section
namespace Lax149335.InjectiveSurjectiveTerms

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory

/-- `f : A → B` is an isomorphism if `f ; f' ≡ id` and `f' ; f ≡ id` for some
`f' : B → A`. -/
def ProvableIso {A B : Ty} (f : Term A B) : Prop :=
  ∃ f' : Term B A, (f ⨟ f') ≡ₜ Term.id A ∧ (f' ⨟ f) ≡ₜ Term.id B

end Lax149335.InjectiveSurjectiveTerms
end
