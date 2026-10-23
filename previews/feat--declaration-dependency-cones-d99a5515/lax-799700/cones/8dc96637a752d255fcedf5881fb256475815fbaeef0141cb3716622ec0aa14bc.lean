-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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

-- Lax799700.ThreeDimMatching
section
namespace Lax799700.ThreeDimMatching

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive tripleSysRel : ℕ → Type where
/-- `xEl a`: `a` belongs to the first class. -/
  | xEl : tripleSysRel 1
/-- `yEl a`: `a` belongs to the second class. -/
  | yEl : tripleSysRel 1
/-- `zEl a`: `a` belongs to the third class. -/
  | zEl : tripleSysRel 1
/-- `trip a b c`: `(a, b, c)` is one of the available triples. -/
  | trip : tripleSysRel 3
  deriving DecidableEq

/-- The relational language of triple systems: three marked classes and a
ternary relation. -/
def tripleSys : FirstOrder.Language :=
  ⟨fun _ => Empty, tripleSysRel⟩

/-- `xEl a`: `a` belongs to the first class. -/
abbrev tsXEl : tripleSys.Relations 1 :=
  .xEl

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [tripleSys.Structure A]

/-- `xEl a`: `a` belongs to the first class.  -/
def TSXEl {A : Type} [tripleSys.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tsXEl ![a0]

end Shorthands

section Matching

variable {A : Type}

end Matching

section Problem

variable (A : Type) [tripleSys.Structure A]

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.ThreeDimMatching
end
