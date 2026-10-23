-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Card
import Mathlib.Order.Minimal

-- Lax199508.GraphClasses
section
namespace Lax199508
end Lax199508

namespace Lax199508.GraphClasses
end Lax199508.GraphClasses
end

-- Lax199508.UniformQuasiWideness
section
namespace Lax199508.UniformQuasiWideness

open Lax199508.GraphClasses

/-- A set of vertices is distance-`r` independent in `G` when every walk
between two distinct members is longer than `r`. -/
def DistIndependent {V : Type*} (G : SimpleGraph V) (r : ℕ) (A : Set V) : Prop :=
  A.Pairwise fun u v => ∀ p : G.Walk u v, r < p.length

end Lax199508.UniformQuasiWideness
end

-- Lax3.ColoredGraphs
section
namespace Lax3.ColoredGraphs

/-- A coloring of the vertices `Fin n` by `L` colors: one set of
vertices per color. Colors need be neither disjoint nor covering, so a
vertex may carry any set of colors. -/
abbrev Coloring (n L : ℕ) : Type := Fin L → Set (Fin n)

/-- The vertices `u` and `v` are within distance `d` in `G`: some walk
from `u` to `v` has length at most `d`. -/
def WithinDist {V : Type*} (G : SimpleGraph V) (d : ℕ) (u v : V) : Prop :=
  ∃ w : G.Walk u v, w.length ≤ d

end Lax3.ColoredGraphs
end

-- Lax3.DistFO
section
namespace Lax3.DistFO.DRank
end Lax3.DistFO.DRank

namespace Lax3.DistFO.IsLocal
end Lax3.DistFO.IsLocal

namespace Lax3.DistFO.rename
end Lax3.DistFO.rename

namespace Lax3.DistFO

open Lax3.ColoredGraphs

set_option linter.dupNamespace false in
/-- Formulas of distance logic over `L`-colored graphs, with `k` free
variables. Variables are `Fin k`, and both quantifiers bind the *new
last* index. Beyond the atoms of first-order logic there are colors and
the two distance atoms, and beyond unrestricted quantification there is
local quantification, which ranges over the vertices within a given
radius of the free variables. -/
inductive DistFO (L : ℕ) : ℕ → Type
  /-- The vertices `i` and `j` are adjacent. -/
  | adj {k : ℕ} (i j : Fin k) : DistFO L k
  /-- The vertices `i` and `j` are equal. -/
  | eq {k : ℕ} (i j : Fin k) : DistFO L k
  /-- The vertex `i` has color `c`. -/
  | color {k : ℕ} (c : Fin L) (i : Fin k) : DistFO L k
  /-- Binary distance atom: the distance between `i` and `j` is at most
  `r`. -/
  | distLe {k : ℕ} (r : ℕ) (i j : Fin k) : DistFO L k
  /-- Unary distance atom: the distance from `i` to the color class `c`
  is smaller than `r`. -/
  | distColorLt {k : ℕ} (r : ℕ) (c : Fin L) (i : Fin k) : DistFO L k
  /-- Negation. -/
  | not {k : ℕ} (φ : DistFO L k) : DistFO L k
  /-- Conjunction. -/
  | and {k : ℕ} (φ ψ : DistFO L k) : DistFO L k
  /-- Unrestricted quantification: there is a vertex satisfying `φ`,
  bound at the last index. -/
  | exU {k : ℕ} (φ : DistFO L (k + 1)) : DistFO L k
  /-- Local quantification: there is a vertex within distance `r` of
  some variable in the guard set `g` satisfying `φ`, bound at the last
  index. The radius and the guard set are part of the syntax; which
  radii are admissible at a given distance rank is the business of
  `DRank`, and the guard set is unconstrained there, as in the
  source. -/
  | exL {k : ℕ} (r : ℕ) (g : Finset (Fin k)) (φ : DistFO L (k + 1)) : DistFO L k

variable {L n : ℕ}

/-- Satisfaction of a formula in the `L`-colored graph `(G, col)` under
the environment `m`. A binary distance atom is a walk-length bound, a
unary one asks for a color-class vertex strictly nearer than `r`, and a
local quantifier ranges over the vertices within `r` of some variable
in its guard set — an empty condition, hence unsatisfiable, when the
set is empty. -/
def Sat (G : SimpleGraph (Fin n)) (col : Coloring n L) :
    {k : ℕ} → (Fin k → Fin n) → DistFO L k → Prop
  | _, m, .adj i j => G.Adj (m i) (m j)
  | _, m, .eq i j => m i = m j
  | _, m, .color c i => m i ∈ col c
  | _, m, .distLe r i j => WithinDist G r (m i) (m j)
  | _, m, .distColorLt r c i => ∃ y ∈ col c, ∃ w : G.Walk (m i) y, w.length < r
  | _, m, .not φ => ¬ Sat G col m φ
  | _, m, .and φ ψ => Sat G col m φ ∧ Sat G col m ψ
  | _, m, .exU φ => ∃ v : Fin n, Sat G col (Fin.snoc m v) φ
  | _, m, .exL r g φ =>
      ∃ v : Fin n, (∃ i ∈ g, WithinDist G r (m i) v) ∧ Sat G col (Fin.snoc m v) φ

end Lax3.DistFO
end

-- Lax3.ScatterSentences
section
namespace Lax3.ScatterSentences

open Lax3.ColoredGraphs Lax3.DistFO Lax199508.UniformQuasiWideness

/-- A choice of scatter values: for every graph `G`, radius `r` and
vertex set `X`, a number `size G r X` which is the cardinality of some
inclusion-wise maximal `r`-scattered subset of `X`. This is the
source's "fix arbitrarily and once and for all a value `s`", made a
parameter: every statement about scatter sentences holds for every
choice. -/
structure ScatterChoice where
  /-- The chosen scatter value of a graph, radius and vertex set. -/
  size : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ → Set (Fin n) → ℕ
  /-- The chosen value is realized by an inclusion-wise maximal
  `r`-scattered subset of `X`. -/
  spec : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)),
    ∃ S : Set (Fin n), S ⊆ X ∧
      Maximal (fun T => T ⊆ X ∧ DistIndependent G r T) S ∧ S.ncard = size G r X

/-- A scatter sentence: there is an `r`-scattered set of `t` vertices
satisfying the one-variable formula `β`, in the sense fixed by a
scatter choice. -/
structure ScatterSentence (L : ℕ) where
  /-- The radius at which the witnesses are scattered. -/
  r : ℕ
  /-- The one-variable formula the witnesses satisfy. -/
  β : DistFO L 1
  /-- The number of witnesses demanded. -/
  t : ℕ

variable {L n : ℕ}

/-- The scatter sentence holds in the colored graph `(G, col)` when the
chosen scatter value of the set defined by `β`, at radius `r`, is at
least `t`. -/
def ScatterSentence.Sat (choice : ScatterChoice) (G : SimpleGraph (Fin n))
    (col : Coloring n L) (σ : ScatterSentence L) : Prop :=
  σ.t ≤ choice.size G σ.r {a | DistFO.Sat G col (fun _ => a) σ.β}

end Lax3.ScatterSentences
end
