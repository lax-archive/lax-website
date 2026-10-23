-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Cardinal.Finite

-- Lax117614.WebsiteGraphs
section
namespace Lax117614.WebsiteGraphs

open FirstOrder

open FirstOrder.Language Structure

/-- The relation symbols of the language. -/
inductive siteGraphRel : ℕ → Type where
/-- `edge a b`: a hyperlink from page `a` to page `b`. -/
  | edge : siteGraphRel 2
/-- `root a`: the page `a` is the crawl's starting point. -/
  | root : siteGraphRel 1
/-- `target a`: the page `a` must be crawled. -/
  | target : siteGraphRel 1
/-- `marked a`: the page `a` belongs to the marked set carrying the
  budget. -/
  | marked : siteGraphRel 1
  deriving DecidableEq

/-- The relational language of website graphs: directed links, a root, a set
of target pages, and a marked set whose cardinality is the crawling budget. -/
def siteGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, siteGraphRel⟩

section Shorthands

variable {A : Type} [siteGraph.Structure A]

end Shorthands

end Lax117614.WebsiteGraphs
end

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

-- Lax117614.GraphCrawlingProblem
section
namespace Lax117614.GraphCrawlingProblem

open FirstOrder

open FirstOrder.Language Structure

open Lax904597.Problems Lax904597.Classes Lax799700.Problems Lax117614.WebsiteGraphs

section Reachability

variable {A : Type}

/-- The directed step available inside a chosen set: an edge whose two
endpoints are both chosen. -/
def DiLink (Adjp : A → A → Prop) (S : A → Prop) (a b : A) : Prop :=
  S a ∧ S b ∧ Adjp a b

/-- Every member of `S` is reachable from `r` by directed steps inside `S` –
the shape of an `r`-rooted subtree with node set `S`, reachability being all a
breadth-first traversal needs to assemble the tree. -/
def ReachesAllOn (Adjp : A → A → Prop) (r : A) (S : A → Prop) : Prop :=
  ∀ x, S x → Relation.ReflTransGen (DiLink Adjp S) r x

end Reachability

section Generic

variable {A : Type}

end Generic

section Problem

variable (A : Type) [siteGraph.Structure A]

end Problem

end Lax117614.GraphCrawlingProblem
end
