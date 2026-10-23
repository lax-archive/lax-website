-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Semantics

-- Lax12.GraphClasses
section
namespace Lax12.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax12.GraphClasses
end

-- Lax12.NowhereDenseClasses
section
namespace Lax12.NowhereDenseClasses

open Lax12.GraphClasses

/-- A model of `H` as a depth-`r` minor of `G`: pairwise disjoint branch
sets, each spanned by walks of length at most `r` from a center vertex
(hence connected of radius at most `r`), with an edge of `G` between the
branch sets of any two adjacent vertices of `H`. -/
structure ShallowMinorModel {V W : Type*} (r : ℕ) (H : SimpleGraph W)
    (G : SimpleGraph V) where
  /-- The branch set of each vertex of `H`. -/
  branch : W → Set V
  /-- The center of each branch set. -/
  center : W → V
  /-- Centers lie in their branch sets (so branch sets are nonempty). -/
  center_mem : ∀ u, center u ∈ branch u
  /-- Distinct branch sets are disjoint. -/
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  /-- Every vertex of a branch set is reached from the center by a walk
  of length at most `r` inside the branch set. -/
  radius_le : ∀ u, ∀ x ∈ branch u, ∃ w : G.Walk (center u) x,
    w.length ≤ r ∧ ∀ y ∈ w.support, y ∈ branch u
  /-- Adjacent vertices of `H` have adjacent branch sets. -/
  adj : ∀ u v, H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

/-- `H` is a minor of `G` at depth `r`. -/
def HasShallowMinor {V W : Type*} (G : SimpleGraph V) (r : ℕ)
    (H : SimpleGraph W) : Prop :=
  Nonempty (ShallowMinorModel r H G)

/-- A graph class is nowhere dense if for every depth `r` some complete
graph is not a depth-`r` minor of any member. -/
def NowhereDense (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ HasShallowMinor G r (⊤ : SimpleGraph (Fin t))

end Lax12.NowhereDenseClasses
end

-- Lax5.GraphClasses
section
namespace Lax5.GraphClasses

open scoped SimpleGraph

open Lax12.GraphClasses

/-- The class of all finite simple graphs. -/
def allGraphs : GraphClass := fun _ _ => True

end Lax5.GraphClasses
end

-- Lax5.Transductions
section
namespace Lax5.Transductions

open FirstOrder

universe u v u' v'

/-- A class of finite structures of the language `L`: for each `n`, a
predicate on the `L`-structures over the canonical `n`-element type. -/
abbrev StructureClass (L : Language.{u, v}) : Type (max u v) :=
  ∀ n : ℕ, L.Structure (Fin n) → Prop

/-- The relation symbols of the color language: `k` unary predicates. -/
inductive ColorRel (k : ℕ) : ℕ → Type
  | color (i : Fin k) : ColorRel k 1

/-- The language consisting of `k` unary color predicates and nothing
else. -/
def colorLanguage (k : ℕ) : Language :=
  ⟨fun _ => Empty, ColorRel k⟩
  deriving Language.IsRelational

/-- The language `L` expanded by `k` unary color predicates. -/
abbrev withColors (L : Language.{u, v}) (k : ℕ) : Language :=
  L.sum (colorLanguage k)

/-- The color sets `colors` as a structure of the color language:
`.color i` holds of the elements of `colors i`. -/
@[implicit_reducible]
def colorStructure {M : Type*} {k : ℕ} (colors : Fin k → Set M) :
    (colorLanguage k).Structure M where
  RelMap | .color i => fun x => x 0 ∈ colors i

/-- The formula `φ` of the colored language holds of the tuple `v` in
the `L`-structure `M` expanded by the color sets `colors`. -/
def RealizeIn {L : Language.{u, v}} {n k : ℕ} (M : L.Structure (Fin n))
    (colors : Fin k → Set (Fin n)) {α : Type*}
    (φ : (withColors L k).Formula α) (v : α → Fin n) : Prop :=
  letI := M
  letI := colorStructure colors
  φ.Realize v

/-- A non-copying transduction from `L`-structures to `L'`-structures:
finitely many unary colors, a domain formula selecting the output
universe, and one formula per relation symbol of the target language. -/
structure Transduction (L : Language.{u, v}) (L' : Language.{u', v'}) where
  /-- The number of unary color predicates. -/
  colors : ℕ
  /-- The formula selecting the elements of the output structure. -/
  domain : (withColors L colors).Formula (Fin 1)
  /-- The formula interpreting each relation symbol of the target. -/
  rel : ∀ {r : ℕ}, L'.Relations r → (withColors L colors).Formula (Fin r)

/-- `C` transduces `D`: a single transduction produces every member of
`D` from some colored member of `C`, up to isomorphism — the embedding
`f` identifies the output structure with the substructure of elements
selected by the domain formula. -/
def Transduces {L : Language.{u, v}} {L' : Language.{u', v'}}
    [L'.IsRelational] (C : StructureClass L) (D : StructureClass L') :
    Prop :=
  ∃ T : Transduction L L',
    ∀ (m : ℕ) (N : L'.Structure (Fin m)), D m N →
      ∃ (n : ℕ) (M : L.Structure (Fin n)), C n M ∧
        ∃ (colors : Fin T.colors → Set (Fin n)) (f : Fin m ↪ Fin n),
          (∀ x : Fin n,
            x ∈ Set.range f ↔ RealizeIn M colors T.domain ![x]) ∧
          ∀ {r : ℕ} (R : L'.Relations r) (v : Fin r → Fin m),
            N.RelMap R v ↔ RealizeIn M colors (T.rel R) (f ∘ v)

end Lax5.Transductions
end

-- Lax5.GraphTransductions
section
namespace Lax5.GraphTransductions

open FirstOrder Lax12.GraphClasses

/-- The members of a graph class, as structures of the language of
graphs: adjacency interprets the binary relation. -/
def structureClass (C : GraphClass) :
    Transductions.StructureClass Language.graph :=
  fun n S => ∃ G : SimpleGraph (Fin n), C n G ∧ S = G.structure

/-- `C` transduces `D` as graph classes: the corresponding classes of
graph structures are related by a first-order transduction. -/
def Transduces (C D : GraphClass) : Prop :=
  Transductions.Transduces (structureClass C) (structureClass D)

end Lax5.GraphTransductions
end

-- Lax5.MonadicDependence
section
namespace Lax5.MonadicDependence

open Lax12.GraphClasses Lax5.GraphClasses

/-- A graph class is monadically dependent if it does not transduce the
class of all finite simple graphs. -/
def MonadicallyDependent (C : GraphClass) : Prop :=
  ¬ GraphTransductions.Transduces C allGraphs

end Lax5.MonadicDependence
end

-- Lax5.AdlerAdler
section
namespace Lax5.AdlerAdler

open Lax12.GraphClasses Lax12.NowhereDenseClasses

open Lax5.MonadicDependence

/-- Nowhere dense graph classes are monadically dependent. -/
axiom monadicallyDependent_of_nowhereDense
    (C : GraphClass) (h : NowhereDense C) :
    MonadicallyDependent C

end Lax5.AdlerAdler
end
