-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax904597.SecondOrder
section
namespace Lax904597.SecondOrder.SORealize
end Lax904597.SecondOrder.SORealize

namespace Lax904597.SecondOrder.soLang
end Lax904597.SecondOrder.soLang

namespace Lax904597.SecondOrder

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A second-order quantifier block: finitely many relation variables, with
given arities. The index type is arbitrary rather than an initial segment of
`ℕ`, so that constructions on blocks can build their natural index types. -/
structure SOBlock : Type 1 where
  /-- The index type of the relation variables of the block. -/
  ι : Type
  /-- A block has finitely many relation variables. -/
  [ιFinite : Finite ι]
  /-- The arity of each relation variable. -/
  arity : ι → ℕ

attribute [instance] SOBlock.ιFinite

/-- The relational vocabulary of a block: one relation symbol per relation
variable. -/
def SOBlock.lang (B : SOBlock) : Language :=
  ⟨fun _ => Empty, fun n => {i : B.ι // B.arity i = n}⟩

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax485149.SecondOrderAtoms
section
namespace Lax485149.SecondOrderAtoms

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- An atom `R i (x_{f 0}, …)` in the relation variables of a block, with
arguments read from `k` universally quantified first-order variables. -/
structure SOAtom (B : SOBlock) (k : ℕ) where
  /-- The relation variable of the block the atom is about. -/
  idx : B.ι
  /-- The arguments, as indices among the `k` universally quantified
  variables. -/
  args : Fin (B.arity idx) → Fin k

variable {B : SOBlock} {k : ℕ}

end Lax485149.SecondOrderAtoms
end

-- Lax904597.Interpretations
section
namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Interpretations.FOInterpretation
end Lax904597.Interpretations.FOInterpretation

namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction
end

-- Lax535992.HornFragment
section
namespace Lax535992.HornFragment.HornProgram
end Lax535992.HornFragment.HornProgram

namespace Lax535992.HornFragment

open Lax485149.SecondOrderAtoms Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A Horn clause over the input vocabulary `L` and the block `B`, with `k`
universally quantified first-order variables: an arbitrary first-order guard
over `L` and a list of second-order body atoms imply the head atom – or `⊥`,
when the head is `none` (a *goal* clause). -/
structure HornClause (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) where
  /-- The first-order guard, over the input vocabulary alone. -/
  guard : L.Formula (Fin k)
  /-- The body: second-order atoms, all of them positive. -/
  body : List (SOAtom B k)
  /-- The head: a second-order atom, or `none` for a goal clause. -/
  head : Option (SOAtom B k)

section Semantics

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {A : Type} [L.Structure A]

end Semantics

end Lax535992.HornFragment
end

-- Lax535992.LeastFixedPoint
section
namespace Lax535992.LeastFixedPoint

open Lax485149.SecondOrderAtoms Lax535992.HornFragment Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

section Derives

variable {Lg : Language.{0, 0}} {B : SOBlock} {k : ℕ}

variable {A : Type} [Lg.Structure A]

/-- The tuples derivable by a system of rules: the least fixed point, as an
inductive predicate. A rule fires when its guard holds and all its body atoms
are already derived, and it derives its head atom. -/
inductive Derives (rules : List (HornClause Lg B k)) :
    (Σ i : B.ι, Fin (B.arity i) → A) → Prop
  | rule {c : HornClause Lg B k} (hc : c ∈ rules) {a : SOAtom B k}
      (ha : c.head = some a) {v : Fin k → A} (hg : c.guard.Realize v)
      (hb : ∀ b ∈ c.body, Derives rules ⟨b.idx, fun j => v (b.args j)⟩) :
      Derives rules ⟨a.idx, fun j => v (a.args j)⟩

end Derives

/-- A definition in FO(LFP), in clausal normal form: a block of relation
variables, a list of rules defining them inductively, and a first-order output
sentence over the vocabulary expanded by the variables, read at the least fixed
point. -/
structure LFPDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the fixed point. -/
  B : SOBlock
  /-- The number of first-order variables shared by the rules. -/
  k : ℕ
  /-- The rules defining the variables. Rules with no head derive nothing. -/
  rules : List (HornClause (L.sum Language.order) B k)
  /-- The first-order output, over the expanded vocabulary – *unrestricted*,
  in particular free to negate fixed-point atoms. -/
  out : ((L.sum Language.order).sum B.lang).Sentence

namespace LFPDef

variable {L : Language.{0, 0}} (d : LFPDef L)

end LFPDef

end Lax535992.LeastFixedPoint
end
