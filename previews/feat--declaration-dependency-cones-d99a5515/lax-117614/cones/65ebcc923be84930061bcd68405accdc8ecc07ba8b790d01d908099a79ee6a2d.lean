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

instance instIsRelationalSiteGraph : FirstOrder.Language.IsRelational siteGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `edge a b`: a hyperlink from page `a` to page `b`. -/
abbrev wsEdge : siteGraph.Relations 2 :=
  .edge

/-- `root a`: the page `a` is the crawl's starting point. -/
abbrev wsRoot : siteGraph.Relations 1 :=
  .root

/-- `target a`: the page `a` must be crawled. -/
abbrev wsTarget : siteGraph.Relations 1 :=
  .target

/-- `marked a`: the page `a` belongs to the marked set carrying the
  budget. -/
abbrev wsMarked : siteGraph.Relations 1 :=
  .marked

section Shorthands

variable {A : Type} [siteGraph.Structure A]

/-- A hyperlink in a website graph. -/
def WSEdge (a b : A) : Prop := RelMap wsEdge ![a, b]

/-- Being the root of a website graph. -/
def WSRoot (a : A) : Prop := RelMap wsRoot ![a]

/-- Being a target page. -/
def WSTarget (a : A) : Prop := RelMap wsTarget ![a]

/-- Belonging to the marked set carrying the budget. -/
def WSMarked (a : A) : Prop := RelMap wsMarked ![a]

end Shorthands

end Lax117614.WebsiteGraphs
end

-- Lax904597.Problems
section
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

end DecisionProblem

end Lax904597.Problems
end

-- Lax799700.Problems
section
namespace Lax799700.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax799700.Problems
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

/-- Some marked root admits a crawl: a set of pages containing the root and
every target, entirely reachable from the root inside itself, of size (the
paper's total cost, at unit page costs) at most the number encoded by the
marked set. -/
def CrawlOn (Adjp : A → A → Prop) (Rp Tp Kp : A → Prop) : Prop :=
  ∃ r, Rp r ∧ ∃ S : A → Prop, S r ∧ (∀ x, Tp x → S x) ∧ ReachesAllOn Adjp r S ∧
    {x | S x}.ncard ≤ {x | Kp x}.ncard

end Generic

section Problem

variable (A : Type) [siteGraph.Structure A]

/-- A website graph admits a crawl within budget: a set of pages containing
the marked root and every target, reachable from the root inside itself, with
at most as many pages as the marked set has elements. (Finiteness of the
universe is part of the property: cardinality thresholds are only meaningful
on finite structures.) -/
def HasCheapCrawl : Prop :=
  Finite A ∧ CrawlOn (WSEdge (A := A)) WSRoot WSTarget WSMarked

end Problem

/-- GRAPH CRAWLING, decision variant at unit page costs: does the website
graph satisfy `HasCheapCrawl`? -/
def GraphCrawling : DecisionProblem siteGraph :=
  DecisionProblem.ofPred HasCheapCrawl

end Lax117614.GraphCrawlingProblem
end
