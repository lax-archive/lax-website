-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
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
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Hom.Set
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

-- Lax799700.Problems
section
namespace Lax799700
end Lax799700

namespace Lax799700.Problems
end Lax799700.Problems

namespace Lax799700.Problems.DecisionProblem
end Lax799700.Problems.DecisionProblem

namespace Lax799700.Problems.DecisionProblem.ofPred
end Lax799700.Problems.DecisionProblem.ofPred
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

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax799700.SetFamily
section
namespace Lax799700.SetFamily

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive setSystemRel : ℕ → Type where
/-- `elem a`: the element `a` belongs to the ground set. -/
  | elem : setSystemRel 1
/-- `fam a`: the element `a` is one of the sets of the family. -/
  | fam : setSystemRel 1
/-- `mem a b`: the ground element `a` belongs to the set `b`. -/
  | mem : setSystemRel 2
/-- `marked a`: the element `a` belongs to the marked set. -/
  | marked : setSystemRel 1
  deriving DecidableEq

/-- The relational language of set systems: a bipartite incidence structure
between ground elements and sets of a family, together with a marked subset of
the universe whose cardinality serves as threshold. -/
def setSystem : FirstOrder.Language :=
  ⟨fun _ => Empty, setSystemRel⟩

instance instIsRelationalSetSystem : FirstOrder.Language.IsRelational setSystem := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `elem a`: the element `a` belongs to the ground set. -/
abbrev ssElem : setSystem.Relations 1 :=
  .elem

/-- `fam a`: the element `a` is one of the sets of the family. -/
abbrev ssFam : setSystem.Relations 1 :=
  .fam

/-- `mem a b`: the ground element `a` belongs to the set `b`. -/
abbrev ssMem : setSystem.Relations 2 :=
  .mem

/-- `marked a`: the element `a` belongs to the marked set. -/
abbrev ssMarked : setSystem.Relations 1 :=
  .marked

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

end Generic

section Problems

section Shorthands

variable {A : Type} [setSystem.Structure A]

/-- `elem a`: the element `a` belongs to the ground set.  -/
def SSElem {A : Type} [setSystem.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ssElem ![a0]

/-- `fam a`: the element `a` is one of the sets of the family.  -/
def SSFam {A : Type} [setSystem.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ssFam ![a0]

/-- `mem a b`: the ground element `a` belongs to the set `b`.  -/
def SSMem {A : Type} [setSystem.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ssMem ![a0, a1]

/-- `marked a`: the element `a` belongs to the marked set.  -/
def SSMarked {A : Type} [setSystem.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap ssMarked ![a0]

end Shorthands

variable (A : Type) [setSystem.Structure A]

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.SetFamily
end

-- Lax280166.CountingSetFamilies
section
namespace Lax280166.CountingSetFamilies

open Lax799700.SetFamily

open FirstOrder

open Language Structure

section Solutions

variable (A : Type) [setSystem.Structure A]

end Solutions

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The subfamily `G` of the `Fp`-sets covers every `Ep`-element and has
exactly as many members as the `Kp`-marked set. -/
def CoverFamOfSizeOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop)
    (G : A → Prop) : Prop :=
  (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    {s | G s}.ncard = {x | Kp x}.ncard

end Generic

section Problems

variable (A : Type) [setSystem.Structure A]

/-- The subfamily `G` is a cover with exactly as many sets as the marked set,
in a finite set system. -/
def SetCoverOfSize (G : A → Prop) : Prop :=
  Finite A ∧ CoverFamOfSizeOn (fun x : A => SSElem x) (fun s => SSFam s)
    (fun x s => SSMem x s) (fun x => SSMarked x) G

end Problems

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

end Generic

open Lax366625.CountingProblems Lax799700.SetFamily

/-- **#Set Cover**, as a counting problem. -/
noncomputable def SharpSetCover : CountingProblem Lax799700.SetFamily.setSystem :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {G : A → Prop // SetCoverOfSize A G}

end Lax280166.CountingSetFamilies
end
