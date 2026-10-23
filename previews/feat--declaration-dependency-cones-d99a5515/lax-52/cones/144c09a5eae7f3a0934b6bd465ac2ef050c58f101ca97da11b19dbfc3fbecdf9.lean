-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Computability.NFA
import Mathlib.ModelTheory.Semantics

-- Lax52.MSOSyntax
section
namespace Lax52
end Lax52

namespace Lax52.MSOSyntax
end Lax52.MSOSyntax

namespace Lax52.MSOSyntax.Formula
end Lax52.MSOSyntax.Formula

namespace Lax52.MSOSyntax.Formula.equal
end Lax52.MSOSyntax.Formula.equal

namespace Lax52.MSOSyntax.Formula.exFO
end Lax52.MSOSyntax.Formula.exFO

namespace Lax52.MSOSyntax.Formula.exSO
end Lax52.MSOSyntax.Formula.exSO

namespace Lax52.MSOSyntax.Formula.falsum
end Lax52.MSOSyntax.Formula.falsum

namespace Lax52.MSOSyntax.Formula.mem
end Lax52.MSOSyntax.Formula.mem

namespace Lax52.MSOSyntax.Formula.neg
end Lax52.MSOSyntax.Formula.neg

namespace Lax52.MSOSyntax.Formula.or
end Lax52.MSOSyntax.Formula.or

namespace Lax52.MSOSyntax.Formula.rel
end Lax52.MSOSyntax.Formula.rel
end

-- Lax52.MSOSemantics
section
namespace Lax52.MSOSemantics
end Lax52.MSOSemantics

namespace Lax52.MSOSemantics.Realize
end Lax52.MSOSemantics.Realize
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
inductive WordRelation (Sigma : Type u) : Nat → Type u
  | letter (a : Sigma) : WordRelation Sigma 1
  | le : WordRelation Sigma 2

/-- The first-order language with order and one unary predicate per letter. -/
def wordLanguage (Sigma : Type u) : FirstOrder.Language.{0, u} where
  Functions := fun _ => Empty
  Relations := WordRelation Sigma

/-- A structure has the relational content of `w` when its unary letter
relations record exactly the letters of `w` and its order relation is the
natural order on positions. -/
def IsWordStructure {Sigma : Type u} (w : List Sigma)
    (S : (wordLanguage Sigma).Structure (Fin w.length)) : Prop :=
  (∀ (a : Sigma) (xs : Fin 1 → Fin w.length),
      @FirstOrder.Language.Structure.RelMap
        (wordLanguage Sigma) (Fin w.length) S 1 (WordRelation.letter a) xs ↔
        w.get (xs 0) = a) ∧
  (∀ xs : Fin 2 → Fin w.length,
      @FirstOrder.Language.Structure.RelMap
        (wordLanguage Sigma) (Fin w.length) S 2 WordRelation.le xs ↔
        xs 0 ≤ xs 1)

end Lax52.WordStructure
end
