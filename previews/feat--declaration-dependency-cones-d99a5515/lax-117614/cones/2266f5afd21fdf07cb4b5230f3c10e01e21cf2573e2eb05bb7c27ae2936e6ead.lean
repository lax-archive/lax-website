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
namespace Lax117614.CrawlInstances.crawlRelBool
end Lax117614.CrawlInstances.crawlRelBool

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

section Decoder

variable (S : FinPresentation siteGraph)

/-- The root pages of a presented website. -/
def crawlRoots : Finset (Fin S.card) :=
  Finset.univ.filter fun x => S.relBool wsRoot ![x]

/-- Decode a presented website whose unique root has been found: read the
links, targets and budget off the tables, the budget clamped to the page
count as the packaging requires. (The root's existence is what makes the
page count positive.) -/
def crawlDecodeAt (r : Fin S.card) : CrawlInstance :=
  ⟨S.card - 1,
    Finset.univ.filter fun p : Fin (S.card - 1 + 1) × Fin (S.card - 1 + 1) =>
      S.relBool wsEdge ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) p.1,
        Fin.cast (Nat.succ_pred_eq_of_pos r.pos) p.2],
    Fin.cast (Nat.succ_pred_eq_of_pos r.pos).symm r,
    Finset.univ.filter fun x : Fin (S.card - 1 + 1) =>
      S.relBool wsTarget ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) x],
    ⟨min ((Finset.univ.filter fun x : Fin (S.card - 1 + 1) =>
        S.relBool wsMarked ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) x]).card)
      (S.card - 1 + 1), by omega⟩⟩

/-- The decoder: `none` unless the site has exactly one root. -/
def crawlDecode : Option CrawlInstance :=
  match (crawlRoots S).sort (· ≤ ·) with
  | [] => none
  | [r] => some (crawlDecodeAt S r)
  | _ :: _ :: _ => none

end Decoder

end Lax117614.CrawlInstances
end
