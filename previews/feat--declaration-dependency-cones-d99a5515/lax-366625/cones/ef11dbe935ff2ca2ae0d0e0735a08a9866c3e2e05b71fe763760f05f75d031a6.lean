-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
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

-- Lax904597.Relativized
section
namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.Relativized.RelFOInterpretation
end Lax904597.Relativized.RelFOInterpretation

namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction
end

-- Lax366625.CountingProblems
section
namespace Lax366625
end Lax366625

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.CountingProblems.CountingProblem
end Lax366625.CountingProblems.CountingProblem

namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction
end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems.CountingProblem.ofFun
end Lax366625.CountingProblems.CountingProblem.ofFun
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

instance instIsRelationalLang (B : SOBlock) : IsRelational B.lang :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- An assignment of actual relations on a universe `A` to the relation
variables of a block. -/
def SOBlock.Assignment (B : SOBlock) (A : Type) : Type :=
  ∀ i : B.ι, (Fin (B.arity i) → A) → Prop

/-- The structure over the block's vocabulary determined by an assignment. -/
@[reducible]
def SOBlock.structure (B : SOBlock) {A : Type} (ρ : B.Assignment A) :
    B.lang.Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {_} r x => ρ r.1 fun j => x (Fin.cast r.2 j)

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax366625.SecondOrderCounting
section
namespace Lax366625.SecondOrderCounting

open Lax366625.CountingProblems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- **The terms of ΣQSO(FO)** over the vocabulary `L`, with free first-order
variables in `α`. A first-order quantifier binds a block of `n` variables at
once, the variables `Sum.inr i` of `α ⊕ Fin n`; a second-order sum binds the
relation variables of a block, the term under it being over the vocabulary
expanded by the block. -/
inductive SQTerm : Language.{0, 0} → Type → Type 1
  /-- A formula: `1` when it holds, `0` when it does not. -/
  | ind {L : Language.{0, 0}} {α : Type} (φ : L.Formula α) : SQTerm L α
  /-- A constant. -/
  | const {L : Language.{0, 0}} {α : Type} (s : ℕ) : SQTerm L α
  /-- A sum. -/
  | add {L : Language.{0, 0}} {α : Type} (s t : SQTerm L α) : SQTerm L α
  /-- A product. -/
  | mul {L : Language.{0, 0}} {α : Type} (s t : SQTerm L α) : SQTerm L α
  /-- `Σx̄. t`: the sum over the `n`-tuples of elements. -/
  | sum {L : Language.{0, 0}} {α : Type} (n : ℕ) (t : SQTerm L (α ⊕ Fin n)) : SQTerm L α
  /-- `Πx̄. t`: the product over the `n`-tuples of elements. -/
  | prod {L : Language.{0, 0}} {α : Type} (n : ℕ) (t : SQTerm L (α ⊕ Fin n)) : SQTerm L α
  /-- `ΣX̄. t`: the sum over the assignments of a block of relation
  variables. -/
  | sosum {L : Language.{0, 0}} {α : Type} (B : SOBlock) (t : SQTerm (L.sum B.lang) α) :
      SQTerm L α

namespace SQTerm

open Classical in
/-- The value of a term in a structure, under a valuation. -/
noncomputable def eval : ∀ {L : Language.{0, 0}} {α : Type}, SQTerm L α →
    ∀ (A : Type) [L.Structure A], (α → A) → ℕ
  | _, _, ind φ, _, _, v => if φ.Realize v then 1 else 0
  | _, _, const s, _, _, _ => s
  | _, _, add s t, A, _, v => s.eval A v + t.eval A v
  | _, _, mul s t, A, _, v => s.eval A v * t.eval A v
  | _, _, sum _ t, A, _, v => ∑ᶠ w : Fin _ → A, t.eval A (Sum.elim v w)
  | _, _, prod _ t, A, _, v => ∏ᶠ w : Fin _ → A, t.eval A (Sum.elim v w)
  | L, _, sosum B t, A, inst, v =>
      ∑ᶠ ρ : B.Assignment A, @eval (L.sum B.lang) _ t A (@sumStructure L _ A inst (B.structure ρ)) v

end SQTerm

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

end Lax366625.SecondOrderCounting
end
