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

instance instCoeFun : CoeFun (DecisionProblem L) fun _ => ∀ (A : Type) [L.Structure A], Prop :=
  ⟨Holds⟩

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
namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction

namespace Lax904597.Interpretations

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A tagged `dim`-dimensional first-order interpretation of `L'` in `L`:
the defining `L`-formula of each relation symbol of `L'`, for each tuple of
tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
argument tuple. -/
structure FOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) where
  /-- The defining `L`-formula of each relation symbol of `L'`, for each tuple
  of tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
  argument tuple. -/
  relFormula : ∀ {n : ℕ}, L'.Relations n → (Fin n → Tag) → L.Formula (Fin n × Fin dim)

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-- The universe of the structure interpreted in `A`: tagged `dim`-tuples. -/
protected def Map (_I : FOInterpretation L L' Tag dim) (A : Type) : Type :=
  Tag × (Fin dim → A)

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The `L'`-structure interpreted in the `L`-structure `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2

end FOInterpretation

section Ordered

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [LE A]

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

instance sumOrderOrderedStructure : (L.sum Language.order).OrderedStructure A :=
  ⟨fun _ => Iff.rfl⟩

end Ordered

end Lax904597.Interpretations
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized

open FirstOrder FirstOrder.Language Lax904597.Problems Lax904597.Interpretations

/-- A relativized interpretation: an interpretation together with the domain
formula of each tag. -/
structure RelFOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ)
    extends FOInterpretation L L' Tag dim where
  /-- The domain formula of each tag: a tagged tuple `(t, ā)` belongs to the
  target universe iff `domFormula t` holds of `ā`. -/
  domFormula : Tag → L.Formula (Fin dim)

namespace RelFOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The universe of the relativized interpretation in `A`: the tagged tuples
whose coordinates satisfy their tag's domain formula. -/
protected def MapRel : Type :=
  {x : Tag × (Fin dim → A) // (I.domFormula x.1).Realize x.2}

/-- The `L'`-structure interpreted on the definable subset. -/
instance mapRelStructure [L'.IsRelational] : L'.Structure (I.MapRel A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1.1).Realize fun p => (xs p.1).1.2 p.2

end RelFOInterpretation

/-- A relativized ordered first-order reduction from `P` to `Q`. -/
structure RelOrderedFOReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L) (Q : DecisionProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : RelFOInterpretation (L.sum Language.order) L' Tag dim
  /-- The definable domain is inhabited: some tagged tuple satisfies its tag's
  domain formula. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (w : Fin dim → A), (toRelInterpretation.domFormula t).Realize w
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toRelInterpretation.MapRel A)

end Lax904597.Relativized
end

-- Lax904597.SecondOrder
section
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

/-- The base vocabulary expanded by the vocabularies of a list of blocks. -/
def soLang (L : Language.{0, 0}) : List SOBlock → Language.{0, 0}
  | [] => L
  | B :: Bs => soLang (L.sum B.lang) Bs

/-- Alternating second-order satisfaction: the sentence obtained from the
first-order kernel `φ` by quantifying the blocks `Bs` alternately,
existentially first when `pol` is `true`, holds in the `L`-structure `A`. -/
def SORealize (L : Language.{0, 0}) (A : Type) [inst : L.Structure A] :
    ∀ (Bs : List SOBlock), (soLang L Bs).Sentence → Bool → Prop
  | [], φ, _ => @Sentence.Realize L A inst φ
  | B :: Bs, φ, true =>
      ∃ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
          Bs φ false
  | B :: Bs, φ, false =>
      ∀ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
          Bs φ true

variable {L : Language.{0, 0}}

/-- A decision problem is `Σₖ`-definable if, on nonempty finite structures, it
is defined by a second-order sentence with `k` alternating blocks of
second-order quantifiers, starting existentially. -/
def SigmaSODefinable [L.IsRelational] (k : ℕ) (P : DecisionProblem L) : Prop :=
  ∃ Bs : List SOBlock, Bs.length = k ∧
    ∃ φ : (soLang L Bs).Sentence,
      ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ SORealize L A Bs φ true

end Lax904597.SecondOrder
end

-- Lax904597.Classes
section
namespace Lax904597.Classes

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

/-- A complexity class: a membership predicate and a hardness predicate on
decision problems, over arbitrary relational vocabularies. -/
structure ComplexityClass where
  /-- The problems belonging to the class. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop
  /-- The problems every problem of the class reduces to. -/
  Hard : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop

variable {L : Language.{0, 0}} [L.IsRelational]

/-- Cofinal hardness for a collection of problems: every problem of the
collection reduces to every relational problem that `P` reduces to. -/
def CofinalHard (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) : Prop :=
  ∀ {L' : Language.{0, 0}} [L'.IsRelational] (S : DecisionProblem L'),
    Nonempty (RelOrderedFOReduction P S) →
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        Mem Q → Nonempty (RelOrderedFOReduction Q S)

/-- The class with the given membership and cofinal hardness. -/
def ComplexityClass.ofMem
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop) :
    ComplexityClass where
  Mem P := Mem P
  Hard P := CofinalHard Mem P

/-- A problem is complete for a class if it belongs to it and is hard for
it. -/
def ComplexityClass.Complete (C : ComplexityClass) (P : DecisionProblem L) : Prop :=
  C.Mem P ∧ C.Hard P

/-- The level `Σₖ₊₁ᵖ` of the polynomial hierarchy: the problems definable with
`k + 1` alternating blocks of second-order quantifiers, existential first. -/
def sigmaLevel (k : ℕ) : ComplexityClass :=
  .ofMem fun P => SigmaSODefinable (k + 1) P

/-- NP is `Σ₁ᵖ`: by definition, the existential-second-order definable
problems (Fagin's theorem). -/
def NP : ComplexityClass := sigmaLevel 0

end Lax904597.Classes
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

/-- The `L`-structure a presentation presents. -/
instance FinPresentation.str {L : Language.{0, 0}} [L.IsRelational] (S : FinPresentation L) :
    L.Structure (Fin S.card) where
  funMap f := isEmptyElim f
  RelMap R x := S.relBool R x = true

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

/-- The website graph a packaged instance encodes: the pages themselves as
universe, the relations the encoder's computations read as propositions. -/
instance crawlStructure (i : CrawlInstance) : siteGraph.Structure (Fin (i.n + 1)) where
  funMap f := isEmptyElim f
  RelMap R x := crawlRelBool i R x = true

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

/-- Graph crawling on well-formed websites: those with exactly one root, the
ones the decoder handles. -/
def WFGraphCrawling : DecisionProblem siteGraph :=
  DecisionProblem.ofPred fun (A : Type) [siteGraph.Structure A] =>
    A ⊨ crawlWFSentence ∧ HasCheapCrawl A

end Lax117614.CrawlInstances
end

-- Lax117614.CrawlDecoding
section
namespace Lax117614.CrawlDecoding

open FirstOrder FirstOrder.Language Structure

open Lax904597.Problems Lax904597.Classes

open Lax117614.WebsiteGraphs Lax117614.GraphCrawlingProblem Lax117614.CrawlInstances

/-- WFGraphCrawling is NP-complete: the restriction to well-formed websites
loses nothing. -/
axiom wfGraphCrawling_NP_complete : NP.Complete WFGraphCrawling

end Lax117614.CrawlDecoding
end
