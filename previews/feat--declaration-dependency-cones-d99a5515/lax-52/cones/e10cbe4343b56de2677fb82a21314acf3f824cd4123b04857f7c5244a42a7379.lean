-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Computability.NFA
import Mathlib.ModelTheory.Semantics

-- Lax52.MSOSyntax
section
namespace Lax52.MSOSyntax

open FirstOrder

universe u v

/-- Monadic second-order formulas over `L`, intrinsically scoped by the numbers
of available first-order and monadic variables. -/
inductive Formula (L : _root_.FirstOrder.Language.{u, v}) : _root_.Nat → _root_.Nat → Type (max u v)
  | falsum {n m : _root_.Nat} : Formula L n m
  | equal {n m : _root_.Nat} : L.Term (_root_.Fin n) → L.Term (_root_.Fin n) → Formula L n m
  | rel {n m k : _root_.Nat} : L.Relations k → (_root_.Fin k → L.Term (_root_.Fin n)) → Formula L n m
  | mem {n m : _root_.Nat} : L.Term (_root_.Fin n) → _root_.Fin m → Formula L n m
  | or {n m : _root_.Nat} : Formula L n m → Formula L n m → Formula L n m
  | neg {n m : _root_.Nat} : Formula L n m → Formula L n m
  | exFO {n m : _root_.Nat} : Formula L (n + 1) m → Formula L n m
  | exSO {n m : _root_.Nat} : Formula L n (m + 1) → Formula L n m

/-- An MSO sentence has no free variables of either sort. -/
abbrev Sentence (L : _root_.FirstOrder.Language.{u, v}) := Formula L 0 0

namespace Formula

variable {L : _root_.FirstOrder.Language.{u, v}} {n m : _root_.Nat}

end Formula

end Lax52.MSOSyntax
end

-- Lax52.MSOSemantics
section
namespace Lax52.MSOSemantics

open FirstOrder

open FirstOrder.Language

open FirstOrder.Language.Structure

open Lax52.MSOSyntax

universe u v w

variable {L : _root_.FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

/-- Extend a valuation by putting a newly bound variable at index zero. -/
def consVal {n : _root_.Nat} (x : M) (v : _root_.Fin n → M) : _root_.Fin (n + 1) → M :=
  Fin.cases x v

/-- Satisfaction of an MSO formula under first-order and monadic valuations. -/
def Realize : {n m : _root_.Nat} → Formula L n m → (_root_.Fin n → M) →
    (_root_.Fin m → _root_.Set M) → Prop
  | _, _, .falsum, _, _ => _root_.False
  | _, _, .equal t₁ t₂, v, _ => t₁.realize v = t₂.realize v
  | _, _, .rel r ts, v, _ => _root_.FirstOrder.Language.Structure.RelMap r (fun i => (ts i).realize v)
  | _, _, .mem t X, v, V => t.realize v ∈ V X
  | _, _, .or phi psi, v, V => Realize phi v V ∨ Realize psi v V
  | _, _, .neg phi, v, V => ¬Realize phi v V
  | _, _, .exFO phi, v, V => ∃ x : M, Realize phi (consVal x v) V
  | _, _, .exSO phi, v, V => ∃ X : _root_.Set M, Realize phi v (consVal X V)

end Lax52.MSOSemantics
end

-- Lax52.WordStructure
section
namespace Lax52.WordStructure

open FirstOrder

open FirstOrder.Language

open Lax52.MSOSyntax

open Lax52.MSOSemantics

universe u

/-- Relation symbols of the language of words over `Sigma`. -/
inductive WordRelation (Sigma : Type u) : _root_.Nat → Type u
  | letter (a : Sigma) : WordRelation Sigma 1
  | le : WordRelation Sigma 2

/-- The first-order language with order and one unary predicate per letter. -/
def wordLanguage (Sigma : Type u) : FirstOrder.Language.{0, u} where
  Functions := fun _ => _root_.Empty
  Relations := WordRelation Sigma

/-- A structure has the relational content of `w` when its unary letter
relations record exactly the letters of `w` and its order relation is the
natural order on positions. -/
def IsWordStructure {Sigma : Type u} (w : _root_.List Sigma)
    (S : (wordLanguage Sigma).Structure (_root_.Fin w.length)) : Prop :=
  (∀ (a : Sigma) (xs : _root_.Fin 1 → _root_.Fin w.length),
      @FirstOrder.Language.Structure.RelMap
        (wordLanguage Sigma) (_root_.Fin w.length) S 1 (WordRelation.letter a) xs ↔
        w.get (xs 0) = a) ∧
  (∀ xs : _root_.Fin 2 → _root_.Fin w.length,
      @FirstOrder.Language.Structure.RelMap
        (wordLanguage Sigma) (_root_.Fin w.length) S 2 WordRelation.le xs ↔
        xs 0 ≤ xs 1)

/-- Satisfaction of a closed MSO sentence by a word, expressed using any
structure with the uniquely determined relational content of that word. -/
def WordModels {Sigma : Type u} (w : _root_.List Sigma)
    (phi : MSOSyntax.Sentence (wordLanguage Sigma)) : Prop :=
  ∀ S : (wordLanguage Sigma).Structure (_root_.Fin w.length), IsWordStructure w S →
    @MSOSemantics.Realize (wordLanguage Sigma) (_root_.Fin w.length) S 0 0 phi
      (fun i : _root_.Fin 0 => Fin.elim0 i) (fun i : _root_.Fin 0 => Fin.elim0 i)

end Lax52.WordStructure
end
