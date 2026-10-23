-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Hom.Set
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

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
namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction
end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems

open Lax904597.Interpretations Lax904597.Problems Lax904597.Relativized

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-- A counting problem: an isomorphism-invariant natural number attached to
every `L`-structure. Only the values on finite structures are ever read. -/
structure CountingProblem [L.IsRelational] where
  /-- The count: `C A` (through the function coercion) is the number attached
  to the structure `A`. -/
  Count : ∀ (A : Type) [L.Structure A], ℕ
  /-- Counting problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → Count A = Count B

namespace CountingProblem

variable {L} [L.IsRelational]

/-- The counting problem given by a number attached to every structure: the
least value it takes on the structures isomorphic to a given one, which is
invariant by construction. When the number is itself invariant, this is the
number. -/
noncomputable def ofFun (f : ∀ (A : Type) [L.Structure A], ℕ) : CountingProblem L where
  Count := fun A _ =>
    sInf {n : ℕ | ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @f B i = n}
  iso_invariant := fun e =>
    congrArg sInf (Set.ext fun _ =>
      ⟨fun ⟨B, i, g, h⟩ => ⟨B, i, e.comp g, h⟩, fun ⟨B, i, g, h⟩ => ⟨B, i, e.symm.comp g, h⟩⟩)

end CountingProblem

variable {L} {L' : Language.{0, 0}}

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

end Lax366625.CountingProblems
end

-- Lax859101.CountingBipartite
section
namespace Lax859101.CountingBipartite

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive bipGraphRel : ℕ → Type where
/-- `left a`: the vertex `a` is on the left side. -/
  | left : bipGraphRel 1
/-- `edge a b`: there is an edge between `a` and `b`; read for `a` on the
  left and `b` on the right. -/
  | edge : bipGraphRel 2
  deriving DecidableEq

/-- The relational language of bipartite graphs given with their bipartition. -/
def bipGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, bipGraphRel⟩

instance instIsRelationalBipGraph : FirstOrder.Language.IsRelational bipGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `left a`: the vertex `a` is on the left side. -/
abbrev bgLeft : bipGraph.Relations 1 :=
  .left

/-- `edge a b`: there is an edge between `a` and `b`; read for `a` on the
  left and `b` on the right. -/
abbrev bgEdge : bipGraph.Relations 2 :=
  .edge

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [bipGraph.Structure A]

/-- `left a`: the vertex `a` is on the left side.  -/
def BGLeft {A : Type} [bipGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bgLeft ![a0]

/-- `edge a b`: there is an edge between `a` and `b`; read for `a` on the
left and `b` on the right.  -/
def BGEdge {A : Type} [bipGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap bgEdge ![a0, a1]

end Shorthands

/-- The set `S` is independent in a bipartite graph: no edge goes from a left
member of `S` to a right member of `S`. -/
def BipIndep (A : Type) [bipGraph.Structure A] (S : A → Prop) : Prop :=
  ∀ x y : A, S x → S y → BGLeft x → ¬BGLeft y → ¬BGEdge x y

open Lax366625.CountingProblems

/-- **#BIS**, as a counting problem. -/
noncomputable def SharpBIS : CountingProblem Lax859101.CountingBipartite.bipGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // BipIndep A S}

end Lax859101.CountingBipartite
end
