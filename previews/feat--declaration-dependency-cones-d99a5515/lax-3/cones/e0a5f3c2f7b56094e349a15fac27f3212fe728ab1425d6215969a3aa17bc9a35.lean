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
end Lax199508.UniformQuasiWideness
end

-- Lax3.ColoredGraphs
section
namespace Lax3
end Lax3

namespace Lax3.ColoredGraphs
end Lax3.ColoredGraphs
end

-- Lax3.DistFO
section
namespace Lax3.DistFO.Sat
end Lax3.DistFO.Sat

namespace Lax3.DistFO.rename
end Lax3.DistFO.rename

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

/-- The scatter sentence has distance rank `(k, q)`: it demands at most
`k + q` witnesses, and for some `1 ≤ i ≤ q` its formula `β` is local of
distance rank `(k + i, q - i)` and its radius lies in the source's
window `4ρ⁻(k + i, q - i) ≤ r ≤ 9 ^ (k + i) · ρ⁻(k + i, q - i)`. -/
def ScatterSentence.DRank (k q : ℕ) (σ : ScatterSentence L) : Prop :=
  σ.t ≤ k + q ∧ ∃ i, 1 ≤ i ∧ i ≤ q ∧ DistFO.IsLocal σ.β ∧
    DistFO.DRank (k + i) (q - i) σ.β ∧
    4 * rhoMinus (k + i) (q - i) ≤ σ.r ∧ σ.r ≤ 9 ^ (k + i) * rhoMinus (k + i) (q - i)

end Lax3.ScatterSentences
end
