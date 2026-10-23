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

/-- An assignment of actual relations on a universe `A` to the relation
variables of a block. -/
def SOBlock.Assignment (B : SOBlock) (A : Type) : Type :=
  ∀ i : B.ι, (Fin (B.arity i) → A) → Prop

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

/-- The truth value of a second-order atom under an assignment of the block
and a valuation of the universally quantified variables. -/
def SOAtom.Holds {A : Type} (a : SOAtom B k) (ρ : B.Assignment A) (v : Fin k → A) : Prop :=
  ρ a.idx fun j => v (a.args j)

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

-- Lax485149.KromFragment
section
namespace Lax485149.KromFragment.KromClause
end Lax485149.KromFragment.KromClause

namespace Lax485149.KromFragment.KromProgram
end Lax485149.KromFragment.KromProgram

namespace Lax485149.KromFragment

open Lax485149.SecondOrderAtoms Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A literal in the relation variables of a block: an atom together with a
sign (`positive = false` for a negated atom). -/
structure KromLit (B : SOBlock) (k : ℕ) where
  /-- The underlying second-order atom. -/
  atom : SOAtom B k
  /-- The sign of the literal: `true` for the atom, `false` for its
  negation. -/
  positive : Bool

section Semantics

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {A : Type} [L.Structure A]

/-- The truth value of a literal: its atom, or the negation of its atom. -/
def KromLit.Holds (l : KromLit B k) (ρ : B.Assignment A) (v : Fin k → A) : Prop :=
  if l.positive then l.atom.Holds ρ v else ¬l.atom.Holds ρ v

end Semantics

variable {L : Language.{0, 0}}

end Lax485149.KromFragment
end
