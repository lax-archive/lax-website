-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Forall2
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
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

-- Lax624099.Problems
section
namespace Lax624099
end Lax624099

namespace Lax624099.Problems
end Lax624099.Problems

namespace Lax624099.Problems.DecisionProblem
end Lax624099.Problems.DecisionProblem

namespace Lax624099.Problems.DecisionProblem.ofPred
end Lax624099.Problems.DecisionProblem.ofPred
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

-- Lax624099.PostCorrespondence
section
namespace Lax624099.PostCorrespondence.Pcp.IsWF
end Lax624099.PostCorrespondence.Pcp.IsWF

namespace Lax624099.PostCorrespondence

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of Post correspondence systems. -/
inductive pcpRel : ℕ → Type
  /-- `le x y`: the order of the positions. -/
  | le : pcpRel 2
  /-- `dom d`: the element `d` is one of the dominoes. -/
  | dom : pcpRel 1
  /-- `uAt d p c`: the top word of the domino `d` has the letter `c` at the
  position `p`. -/
  | uAt : pcpRel 3
  /-- `vAt d p c`: the bottom word of the domino `d` has the letter `c` at the
  position `p`. -/
  | vAt : pcpRel 3
  deriving DecidableEq

/-- The relational vocabulary of Post correspondence systems: marked dominoes
carrying two words each, over a universe ordered by the order of the positions
of those words. -/
def pcp : Language :=
  ⟨fun _ => Empty, pcpRel⟩

instance instIsRelationalPcp : IsRelational pcp :=
  fun _ => ⟨fun f => Empty.elim f⟩

open FirstOrder

open Language Structure

namespace Pcp

section Reading

variable {A : Type} [pcp.Structure A]

end Reading

section Words

variable {A : Type} [pcp.Structure A]

end Words

end Pcp

open Lax904597.Problems Lax624099.Problems

end Lax624099.PostCorrespondence
end
