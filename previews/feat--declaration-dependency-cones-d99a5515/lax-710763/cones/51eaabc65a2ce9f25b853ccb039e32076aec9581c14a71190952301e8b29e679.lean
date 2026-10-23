-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.Logic.Embedding.Basic
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Semantics

-- Lax199508.GraphClasses
section
namespace Lax199508.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax199508.GraphClasses
end

-- Lax199508.NeighborhoodComplexity
section
namespace Lax199508.NeighborhoodComplexity

open Lax199508.GraphClasses

/-- The number of distinct neighborhood traces `N(v) ∩ A` that the
vertices of `G` leave on the vertex set `A`. -/
noncomputable def traceCount {V : Type*} (G : SimpleGraph V)
    (A : Set V) : ℕ :=
  {S : Set V | ∃ v : V, S = G.neighborSet v ∩ A}.ncard

/-- Every graph in the class leaves at most `c · |A|^(1+ε)` neighborhood
traces on every nonempty vertex subset `A`, where `c` depends only on
`ε > 0`: neighborhood complexity `|A|^(1+o(1))`. -/
def HasAlmostLinearNC (C : GraphClass) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Set (Fin n), A.Nonempty →
        (traceCount G A : ℝ) ≤ c * (A.ncard : ℝ) ^ (1 + ε)

end Lax199508.NeighborhoodComplexity
end

-- Lax710763.GraphClasses
section
namespace Lax710763.GraphClasses

open scoped SimpleGraph

open Lax199508.GraphClasses

/-- The class of all finite simple graphs. -/
def allGraphs : GraphClass := fun _ _ => True

end Lax710763.GraphClasses
end

-- Lax710763.Transductions
section
namespace Lax710763.Transductions

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

end Lax710763.Transductions
end

-- Lax710763.GraphTransductions
section
namespace Lax710763.GraphTransductions

open FirstOrder Lax199508.GraphClasses

/-- The members of a graph class, as structures of the language of
graphs: adjacency interprets the binary relation. -/
def structureClass (C : GraphClass) :
    Transductions.StructureClass Language.graph :=
  fun n S => ∃ G : SimpleGraph (Fin n), C n G ∧ S = G.structure

/-- `C` transduces `D` as graph classes: the corresponding classes of
graph structures are related by a first-order transduction. -/
def Transduces (C D : GraphClass) : Prop :=
  Transductions.Transduces (structureClass C) (structureClass D)

end Lax710763.GraphTransductions
end

-- Lax710763.MonadicDependence
section
namespace Lax710763.MonadicDependence

open Lax199508.GraphClasses Lax710763.GraphClasses

/-- A graph class is monadically dependent if it does not transduce the
class of all finite simple graphs. -/
def MonadicallyDependent (C : GraphClass) : Prop :=
  ¬ GraphTransductions.Transduces C allGraphs

end Lax710763.MonadicDependence
end

-- Lax710763.AlmostLinearNC
section
namespace Lax710763.AlmostLinearNC

open Lax199508.GraphClasses Lax199508.NeighborhoodComplexity Lax710763.MonadicDependence

/-- Monadically dependent graph classes have almost linear neighborhood
complexity. -/
axiom hasAlmostLinearNC_of_monadicallyDependent
    (C : GraphClass) (h : MonadicallyDependent C) :
    HasAlmostLinearNC C

end Lax710763.AlmostLinearNC
end
