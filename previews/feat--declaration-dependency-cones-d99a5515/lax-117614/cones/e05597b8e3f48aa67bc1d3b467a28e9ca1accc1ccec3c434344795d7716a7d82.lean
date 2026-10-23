-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

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

/-- `root a`: the page `a` is the crawl's starting point. -/
abbrev wsRoot : siteGraph.Relations 1 :=
  .root

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
end Lax117614.GraphCrawlingProblem
end

-- Lax117614.CrawlInstances
section
namespace Lax117614.CrawlInstances.crawlDecode
end Lax117614.CrawlInstances.crawlDecode

namespace Lax117614.CrawlInstances.crawlSize
end Lax117614.CrawlInstances.crawlSize

namespace Lax117614.CrawlInstances

open FirstOrder

open FirstOrder.Language Structure

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

open Lax117614.WebsiteGraphs Lax117614.GraphCrawlingProblem

/-- A concretely presented finite `L`-structure: a size and a computable
relation table. This is the input type of decoders – the “raw bytes” a
decoding computation reads. -/
structure FinPresentation (L : Language.{0, 0}) where
  /-- The number of elements. -/
  card : ℕ
  /-- The relations, as computations on `Fin card`. -/
  relBool : ∀ {n}, L.Relations n → (Fin n → Fin card) → Bool

/-- A packaged concrete crawling instance: `n + 1` pages, the hyperlinks, the
root page, the target pages, and the budget (clamped to `n + 1` by its type:
a crawl never has more pages than the site). -/
structure CrawlInstance where
  /-- The page count, minus one: pages are `Fin (n + 1)`, so a website is
  never empty. -/
  n : ℕ
  /-- The hyperlinks. -/
  edges : Finset (Fin (n + 1) × Fin (n + 1))
  /-- The root page, where crawls start. -/
  root : Fin (n + 1)
  /-- The target pages. -/
  targets : Finset (Fin (n + 1))
  /-- The budget, clamped by its type: a crawl never has more pages than the
  site. -/
  budget : Fin (n + 2)
  deriving DecidableEq

/-- The encoder, standalone and auditable: a plain `def`, so the compiler
vouches that it computes. -/
def crawlRelBool (i : CrawlInstance) {n : ℕ} (R : siteGraph.Relations n) :
    (Fin n → Fin (i.n + 1)) → Bool :=
  match n, R with
  | _, .edge => fun x => decide ((x 0, x 1) ∈ i.edges)
  | _, .root => fun x => decide (x 0 = i.root)
  | _, .target => fun x => decide (x 0 ∈ i.targets)
  | _, .marked => fun x => decide ((x 0).1 < i.budget.1)

/-- Well-formedness of a website graph: exactly one root page. What makes an
honest decoder possible. -/
noncomputable def crawlWFSentence : siteGraph.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 1)
  (FirstOrder.Language.Relations.formula₁ wsRoot (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ wsRoot
          (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0))))))

section Decoder

variable (S : FinPresentation siteGraph)

end Decoder

end Lax117614.CrawlInstances
end
