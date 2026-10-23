-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.NFA
import Mathlib.ModelTheory.Semantics

-- Lax146103.MSOSyntax
section
namespace Lax146103
end Lax146103

namespace Lax146103.MSOSyntax
end Lax146103.MSOSyntax

namespace Lax146103.MSOSyntax.Formula
end Lax146103.MSOSyntax.Formula

namespace Lax146103.MSOSyntax.Formula.equal
end Lax146103.MSOSyntax.Formula.equal

namespace Lax146103.MSOSyntax.Formula.exFO
end Lax146103.MSOSyntax.Formula.exFO

namespace Lax146103.MSOSyntax.Formula.exSO
end Lax146103.MSOSyntax.Formula.exSO

namespace Lax146103.MSOSyntax.Formula.falsum
end Lax146103.MSOSyntax.Formula.falsum

namespace Lax146103.MSOSyntax.Formula.mem
end Lax146103.MSOSyntax.Formula.mem

namespace Lax146103.MSOSyntax.Formula.neg
end Lax146103.MSOSyntax.Formula.neg

namespace Lax146103.MSOSyntax.Formula.or
end Lax146103.MSOSyntax.Formula.or

namespace Lax146103.MSOSyntax.Formula.rel
end Lax146103.MSOSyntax.Formula.rel
end

-- Lax146103.MSOSemantics
section
namespace Lax146103.MSOSemantics
end Lax146103.MSOSemantics

namespace Lax146103.MSOSemantics.Realize
end Lax146103.MSOSemantics.Realize
end

-- Lax146103.WordStructure
section
namespace Lax146103.WordStructure

open FirstOrder

open FirstOrder.Language

open Lax146103.MSOSyntax

open Lax146103.MSOSemantics

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

end Lax146103.WordStructure
end
