-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.FinRange
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

/-- The ball of radius `r` around `v` in `G`: the vertices within
distance `r` of `v`. -/
def ball {V : Type*} (G : SimpleGraph V) (r : ℕ) (v : V) : Set V :=
  {u | WithinDist G r v u}

end Lax3.ColoredGraphs
end

-- Lax3.DistFO
section
namespace Lax3.DistFO

open Lax3.ColoredGraphs

/-- The lower horizon function ρ⁻ of the source: the largest radius a
distance atom of distance rank `(k, q)` may carry. -/
def rhoMinus (k q : ℕ) : ℕ := 9 ^ ((k + q + 1) * q)

/-- The upper horizon function ρ⁺ of the source: the largest radius a
local quantifier may guard at, one rank level in. -/
def rhoPlus (k q : ℕ) : ℕ := 9 ^ ((k + q) * (q + 1))

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

/-- Renaming of variables along `f`. Under a binder the renaming is
lifted to `Fin (k + 1) → Fin (k' + 1)` by sending the bound variable —
the last index — to the new last index. The guard set of a local
quantifier is mapped along `f`, so a guard keeps naming the same
variables it named before. -/
def rename : {k k' : ℕ} → (Fin k → Fin k') → DistFO L k → DistFO L k'
  | _, _, f, .adj i j => .adj (f i) (f j)
  | _, _, f, .eq i j => .eq (f i) (f j)
  | _, _, f, .color c i => .color c (f i)
  | _, _, f, .distLe r i j => .distLe r (f i) (f j)
  | _, _, f, .distColorLt r c i => .distColorLt r c (f i)
  | _, _, f, .not φ => .not (rename f φ)
  | _, _, f, .and φ ψ => .and (rename f φ) (rename f ψ)
  | _, k', f, .exU φ => .exU (rename (Fin.snoc (fun i => (f i).castSucc) (Fin.last k')) φ)
  | _, k', f, .exL r g φ =>
      .exL r (g.image f) (rename (Fin.snoc (fun i => (f i).castSucc) (Fin.last k')) φ)

/-- `DRank k' q φ` says that `φ` has distance rank `(k', q)`: its
quantifier rank is at most `q`, every distance atom in it has radius at
most `ρ⁻` of the rank in force there, and every local quantifier guards
at radius at most `ρ⁺` of the rank one level in. The rank argument
`k'` is a bound on the number of free variables and is independent of
the type index. -/
inductive DRank {L : ℕ} : ℕ → ℕ → {k : ℕ} → DistFO L k → Prop
  /-- An adjacency atom has every distance rank. -/
  | adj {k' q k : ℕ} (i j : Fin k) : DRank k' q (.adj i j)
  /-- An equality atom has every distance rank. -/
  | eq {k' q k : ℕ} (i j : Fin k) : DRank k' q (.eq i j)
  /-- A color atom has every distance rank. -/
  | color {k' q k : ℕ} (c : Fin L) (i : Fin k) : DRank k' q (.color c i)
  /-- A binary distance atom has distance rank `(k', q)` when its
  radius is at most `ρ⁻(k', q)`. -/
  | distLe {k' q k : ℕ} {r : ℕ} (i j : Fin k) (hr : r ≤ rhoMinus k' q) :
      DRank k' q (.distLe r i j)
  /-- A unary distance atom has distance rank `(k', q)` when its radius
  is at most `ρ⁻(k', q)`. -/
  | distColorLt {k' q k : ℕ} {r : ℕ} (c : Fin L) (i : Fin k) (hr : r ≤ rhoMinus k' q) :
      DRank k' q (.distColorLt r c i)
  /-- Negation preserves the distance rank. -/
  | not {k' q k : ℕ} {φ : DistFO L k} (h : DRank k' q φ) : DRank k' q (.not φ)
  /-- Conjunction preserves the distance rank. -/
  | and {k' q k : ℕ} {φ ψ : DistFO L k} (h : DRank k' q φ) (h' : DRank k' q ψ) :
      DRank k' q (.and φ ψ)
  /-- An unrestricted quantifier has distance rank `(k', q + 1)` when
  its body has distance rank `(k' + 1, q)`. -/
  | exU {k' q k : ℕ} {φ : DistFO L (k + 1)} (h : DRank (k' + 1) q φ) :
      DRank k' (q + 1) (.exU φ)
  /-- A local quantifier has distance rank `(k', q + 1)` when its body
  has distance rank `(k' + 1, q)` and it guards at radius at most
  `ρ⁺(k' + 1, q)`. The guard set is unconstrained. -/
  | exL {k' q k : ℕ} {r : ℕ} {g : Finset (Fin k)} {φ : DistFO L (k + 1)}
      (h : DRank (k' + 1) q φ) (hr : r ≤ rhoPlus (k' + 1) q) : DRank k' (q + 1) (.exL r g φ)

/-- A formula is local when it uses no unrestricted quantification. -/
def IsLocal : {k : ℕ} → DistFO L k → Prop
  | _, .adj _ _ => True
  | _, .eq _ _ => True
  | _, .color _ _ => True
  | _, .distLe _ _ _ => True
  | _, .distColorLt _ _ _ => True
  | _, .not φ => IsLocal φ
  | _, .and φ ψ => IsLocal φ ∧ IsLocal ψ
  | _, .exU _ => False
  | _, .exL _ _ φ => IsLocal φ

/-- The vertices `u` and `v` are within distance `d` *inside* `D`: some
walk from `u` to `v` has length at most `d` and stays in `D`. This is
the walk distance of the substructure induced on `D`, with the carrier
kept. -/
def WithinDistIn {V : Type*} (D : Set V) (G : SimpleGraph V) (d : ℕ) (u v : V) : Prop :=
  ∃ w : G.Walk u v, w.length ≤ d ∧ ∀ x ∈ w.support, x ∈ D

/-- Satisfaction in the substructure induced on `D`, with the carrier
kept: quantifiers range over `D`, an edge counts only if both endpoints
lie in `D`, color classes are intersected with `D`, and distances are
measured along walks inside `D`. -/
def SatWithin (D : Set (Fin n)) (G : SimpleGraph (Fin n)) (col : Coloring n L) :
    {k : ℕ} → (Fin k → Fin n) → DistFO L k → Prop
  | _, m, .adj i j => G.Adj (m i) (m j) ∧ m i ∈ D ∧ m j ∈ D
  | _, m, .eq i j => m i = m j
  | _, m, .color c i => m i ∈ col c ∧ m i ∈ D
  | _, m, .distLe r i j => WithinDistIn D G r (m i) (m j)
  | _, m, .distColorLt r c i =>
      ∃ y, y ∈ col c ∧ y ∈ D ∧ ∃ w : G.Walk (m i) y, w.length < r ∧ ∀ x ∈ w.support, x ∈ D
  | _, m, .not φ => ¬ SatWithin D G col m φ
  | _, m, .and φ ψ => SatWithin D G col m φ ∧ SatWithin D G col m ψ
  | _, m, .exU φ => ∃ v ∈ D, SatWithin D G col (Fin.snoc m v) φ
  | _, m, .exL r g φ =>
      ∃ v ∈ D, (∃ i ∈ g, WithinDistIn D G r (m i) v) ∧ SatWithin D G col (Fin.snoc m v) φ

/-- A formula is semantically `r`-local when its truth on a tuple never
depends on the vertices further than `r` from that tuple: satisfaction
in the graph and satisfaction in the substructure induced on the union
of the `r`-balls around the tuple agree, in every colored graph and at
every tuple. -/
def SemanticallyLocal (r : ℕ) {k : ℕ} (φ : DistFO L k) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
    Sat G col m φ ↔ SatWithin (⋃ i, ball G r (m i)) G col m φ

end Lax3.DistFO
end

-- Lax3.ScatterSentences
section
namespace Lax3.ScatterSentences.ScatterChoice
end Lax3.ScatterSentences.ScatterChoice

namespace Lax3.ScatterSentences

open Lax3.ColoredGraphs Lax3.DistFO Lax199508.UniformQuasiWideness

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

end Lax3.ScatterSentences
end

-- Lax3.Locality
section
namespace Lax3.Locality

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences

universe u

/-- Boolean combinations of atoms drawn from `α`. Disjunction and
implication are the usual abbreviations; the empty combination is
`tru`. -/
inductive BC (α : Type u) : Type u
  /-- An atom. -/
  | atom (a : α) : BC α
  /-- The empty combination, always true. -/
  | tru : BC α
  /-- Negation. -/
  | not (b : BC α) : BC α
  /-- Conjunction. -/
  | and (b c : BC α) : BC α

/-- The truth value of a boolean combination, given a truth value for
each atom. -/
def BC.eval {α : Type u} (v : α → Prop) : BC α → Prop
  | .atom a => v a
  | .tru => True
  | .not b => ¬ BC.eval v b
  | .and b c => BC.eval v b ∧ BC.eval v c

/-- The atoms occurring in a boolean combination, with multiplicity. -/
def BC.atoms {α : Type u} : BC α → List α
  | .atom a => [a]
  | .tru => []
  | .not b => BC.atoms b
  | .and b c => BC.atoms b ++ BC.atoms c

variable {L : ℕ}

end Lax3.Locality
end

-- Lax3.NormalForm
section
namespace Lax3.NormalForm

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality

variable {L : ℕ}

/-- A formula that holds in every colored graph under every
environment: no vertex differs from itself. -/
def verum {k : ℕ} : DistFO L k :=
  .not (.exU (.not (.eq (Fin.last k) (Fin.last k))))

/-- The conjunction of a list of formulas; the empty conjunction is
`verum`. -/
def conj {k : ℕ} : List (DistFO L k) → DistFO L k
  | [] => verum
  | φ :: φs => .and φ (conj φs)

/-- `k` unrestricted quantifiers in front of a formula with `k` free
variables, leaving a sentence. -/
def exUs : {k : ℕ} → DistFO L k → DistFO L 0
  | 0, φ => φ
  | _ + 1, φ => exUs (.exU φ)

/-- The source's scatter sentence written out in distance logic: there
are `t` vertices, pairwise at distance larger than `r`, each satisfying
`β`. Distance larger than `r` is the negation of the binary distance
atom of radius `r`, and `β` is placed at each bound variable by
renaming. -/
def scatterFml (r t : ℕ) (β : DistFO L 1) : DistFO L 0 :=
  exUs (conj
    (((List.finRange t).flatMap fun i =>
        (List.finRange t).filterMap fun j =>
          if i = j then none else some (DistFO.not (DistFO.distLe r i j))) ++
      (List.finRange t).map fun i => rename (fun _ : Fin 1 => i) β))

/-- **Normal form for distance logic** (Corollary 7 of
arXiv:2606.23180). For `q ≥ 1`, every formula of distance rank `(k, q)`
is equivalent to a boolean combination of local formulas of distance
rank `(k, q)` and sentences `scatterFml r t β` — there are `t` vertices,
pairwise at distance larger than `r`, all satisfying `β` — where
`t ≤ k + q`, the formula `β` is local of distance rank `(k + 1, q - 1)`,
the radius satisfies `r ≤ ρ⁻(k, q)`, and `β` is semantically
`r / 4`-local. -/
axiom normalForm {k q : ℕ} (hq : 1 ≤ q) (φ : DistFO L k) (hφ : DistFO.DRank k q φ) :
    ∃ b : BC (DistFO L k ⊕ ScatterSentence L),
      (∀ ψ : DistFO L k, Sum.inl ψ ∈ b.atoms → DistFO.IsLocal ψ ∧ DistFO.DRank k q ψ) ∧
      (∀ σ : ScatterSentence L, Sum.inr σ ∈ b.atoms →
        σ.t ≤ k + q ∧ DistFO.IsLocal σ.β ∧ DistFO.DRank (k + 1) (q - 1) σ.β ∧
          σ.r ≤ rhoMinus k q ∧ DistFO.SemanticallyLocal (σ.r / 4) σ.β) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n L) (m : Fin k → Fin n),
        DistFO.Sat G col m φ ↔
          b.eval (Sum.elim (DistFO.Sat G col m)
            (fun σ => DistFO.Sat G col Fin.elim0 (scatterFml σ.r σ.t σ.β)))

end Lax3.NormalForm
end
